import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4816 = true := by
  decide +kernel

theorem tot4816 : totK PA10K2 A10K2.t4816 = [0, 0, 119048527108, 1004786274021, 2198365034148, 1447374515633, 220128021645, 6632180018, 0, 0] := by
  decide +kernel

theorem rows4817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4817 = true := by
  decide +kernel

theorem tot4817 : totK PA10K2 A10K2.t4817 = [0, 0, 404282802835, 1566756278167, 2011080746391, 877371217492, 81954502599, 0, 0, 0] := by
  decide +kernel

theorem rows4818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4818 = true := by
  decide +kernel

theorem tot4818 : totK PA10K2 A10K2.t4818 = [0, 0, 377671617764, 1641675430098, 2099010664952, 806011371115, 71686403169, 0, 0, 0] := by
  decide +kernel

theorem rows4819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4819 = true := by
  decide +kernel

theorem tot4819 : totK PA10K2 A10K2.t4819 = [0, 0, 105375790585, 878359806955, 2070441313566, 1571801104844, 267877023908, 7047025452, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
