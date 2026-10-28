import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t504 = true := by
  decide +kernel

theorem tot504 : totK PA10K2 A10K2.t504 = [0, 0, 479271173950, 1905776158271, 2125751073449, 573817274621, 12926121504, 0, 0, 0] := by
  decide +kernel

theorem rows505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t505 = true := by
  decide +kernel

theorem tot505 : totK PA10K2 A10K2.t505 = [0, 0, 575964859727, 1883026384263, 1723553713439, 505091671729, 54615487832, 0, 0, 0] := by
  decide +kernel

theorem rows506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t506 = true := by
  decide +kernel

theorem tot506 : totK PA10K2 A10K2.t506 = [0, 0, 259431729192, 1462743110064, 2223108485686, 842987926430, 62227247501, 0, 0, 0] := by
  decide +kernel

theorem rows507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t507 = true := by
  decide +kernel

theorem tot507 : totK PA10K2 A10K2.t507 = [0, 0, 0, 514364427165, 1818082131363, 1749478952930, 475915995284, 31018567651, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
