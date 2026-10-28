import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5260 = true := by
  decide +kernel

theorem tot5260 : totK PA10K2 A10K2.t5260 = [0, 0, 479936357897, 1770563022079, 2017763570466, 654545149416, 42633500131, 0, 0, 0] := by
  decide +kernel

theorem rows5261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5261 = true := by
  decide +kernel

theorem tot5261 : totK PA10K2 A10K2.t5261 = [0, 0, 464068089441, 1871485081107, 1926184390604, 452591371460, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows5262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5262 = true := by
  decide +kernel

theorem tot5262 : totK PA10K2 A10K2.t5262 = [0, 0, 249045368514, 1222370741545, 2105916771273, 1080169373269, 111186545994, 0, 0, 0] := by
  decide +kernel

theorem rows5263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5263 = true := by
  decide +kernel

theorem tot5263 : totK PA10K2 A10K2.t5263 = [0, 0, 97204760165, 648549900348, 1772174919470, 1591491226610, 444171710487, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
