import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t416 = true := by
  decide +kernel

theorem tot416 : totK PA10K2 A10K2.t416 = [505834502873, 1687106493133, 1690218956697, 664758692702, 128808735772, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t417 = true := by
  decide +kernel

theorem tot417 : totK PA10K2 A10K2.t417 = [304053839609, 1450064242917, 2054213753501, 796488677644, 59762371672, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t418 = true := by
  decide +kernel

theorem tot418 : totK PA10K2 A10K2.t418 = [0, 696098333995, 2112476204479, 1533211209883, 264240965699, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t419 = true := by
  decide +kernel

theorem tot419 : totK PA10K2 A10K2.t419 = [0, 467140627321, 1861734193923, 1968954794142, 465750975426, 25633273041, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
