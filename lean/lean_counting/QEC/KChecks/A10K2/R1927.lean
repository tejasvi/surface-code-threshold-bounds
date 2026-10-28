import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7708 = true := by
  decide +kernel

theorem tot7708 : totK PA10K2 A10K2.t7708 = [0, 0, 277969155514, 1138730342811, 1927432969117, 1428552481737, 276440997500, 5963379153, 0, 0] := by
  decide +kernel

theorem rows7709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7709 = true := by
  decide +kernel

theorem tot7709 : totK PA10K2 A10K2.t7709 = [0, 0, 283187016794, 1467520706877, 2152817648132, 819475337424, 65319300468, 0, 0, 0] := by
  decide +kernel

theorem rows7710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7710 = true := by
  decide +kernel

theorem tot7710 : totK PA10K2 A10K2.t7710 = [0, 0, 299638544946, 1080427707177, 1682849918223, 1312096767053, 269452623405, 10760911071, 0, 0] := by
  decide +kernel

theorem rows7711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7711 = true := by
  decide +kernel

theorem tot7711 : totK PA10K2 A10K2.t7711 = [0, 0, 467509483720, 1774965575246, 1974140475010, 590817869586, 32846095359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
