import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1220 = true := by
  decide +kernel

theorem tot1220 : totK PA10K2 A10K2.t1220 = [0, 315590801309, 783144081635, 706925934401, 1177799618454, 1375665840324, 524050951125, 41417404726, 0, 0] := by
  decide +kernel

theorem rows1221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1221 = true := by
  decide +kernel

theorem tot1221 : totK PA10K2 A10K2.t1221 = [0, 455850589584, 1774143845310, 2013994665294, 570448799039, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1222 = true := by
  decide +kernel

theorem tot1222 : totK PA10K2 A10K2.t1222 = [0, 70106472963, 813811627019, 1996483480252, 1527911910997, 360766963991, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1223 = true := by
  decide +kernel

theorem tot1223 : totK PA10K2 A10K2.t1223 = [0, 212862030042, 1046631913072, 1912333573145, 1373134459840, 231233056540, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
