import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4892 = true := by
  decide +kernel

theorem tot4892 : totK PA10K2 A10K2.t4892 = [0, 120560780508, 1053952141586, 2160233191815, 1472171705625, 256403501112, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4893 = true := by
  decide +kernel

theorem tot4893 : totK PA10K2 A10K2.t4893 = [320561472736, 788898870175, 710824029499, 1192458056992, 1438220810094, 560865471528, 49137536365, 0, 0, 0] := by
  decide +kernel

theorem rows4894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4894 = true := by
  decide +kernel

theorem tot4894 : totK PA10K2 A10K2.t4894 = [420041395616, 1735077047821, 2026366721523, 598679709291, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4895 = true := by
  decide +kernel

theorem tot4895 : totK PA10K2 A10K2.t4895 = [107720792190, 887853558758, 1989583430466, 1469980328651, 329937683481, 20340910120, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
