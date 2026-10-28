import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6600 = true := by
  decide +kernel

theorem tot6600 : totK PA10K2 A10K2.t6600 = [0, 195375731097, 513074386091, 254943154583, 584422216535, 1620864764022, 1098091430947, 203361510298, 6354482628, 0] := by
  decide +kernel

theorem rows6601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6601 = true := by
  decide +kernel

theorem tot6601 : totK PA10K2 A10K2.t6601 = [0, 581234117768, 1956100628727, 1910210059669, 513893108486, 31662601151, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6602 = true := by
  decide +kernel

theorem tot6602 : totK PA10K2 A10K2.t6602 = [0, 0, 746593169507, 2141017524165, 1625303212663, 376199699374, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows6603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6603 = true := by
  decide +kernel

theorem tot6603 : totK PA10K2 A10K2.t6603 = [0, 284639743112, 1398508207164, 2190988496917, 1039202858494, 106784820427, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
