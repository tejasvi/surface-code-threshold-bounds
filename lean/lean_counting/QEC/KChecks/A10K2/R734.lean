import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2936 = true := by
  decide +kernel

theorem tot2936 : totK PA10K2 A10K2.t2936 = [0, 320910162593, 1467253517184, 2195190801472, 997764952164, 83062405637, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2937 = true := by
  decide +kernel

theorem tot2937 : totK PA10K2 A10K2.t2937 = [0, 0, 537416678065, 2021271197606, 2111720701413, 476785725916, 13229391832, 0, 0, 0] := by
  decide +kernel

theorem rows2938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2938 = true := by
  decide +kernel

theorem tot2938 : totK PA10K2 A10K2.t2938 = [0, 0, 406969683961, 1521808131327, 1990779174465, 813549163503, 74697281255, 0, 0, 0] := by
  decide +kernel

theorem rows2939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2939 = true := by
  decide +kernel

theorem tot2939 : totK PA10K2 A10K2.t2939 = [0, 0, 369304560902, 1709750898088, 2137726793594, 735322480760, 54988458253, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
