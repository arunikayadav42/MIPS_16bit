
# PlanAhead Launch Script for Post-Synthesis pin planning, created by Project Navigator

create_project -name mips_mini -dir "D:/mips_mini/planAhead_run_1" -part xc6slx16csg324-3
set_property design_mode GateLvl [get_property srcset [current_run -impl]]
set_property edif_top_file "D:/mips_mini/top.ngc" [ get_property srcset [ current_run ] ]
add_files -norecurse { {D:/mips_mini} }
set_param project.pinAheadLayout  yes
set_property target_constrs_file "top.ucf" [current_fileset -constrset]
add_files [list {top.ucf}] -fileset [get_property constrset [current_run]]
link_design
