import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t644 = true := by
  decide +kernel

theorem tot644 : totK PA10K2 A10K2.t644 = [0, 0, 297225354374, 1209927332297, 1933136757689, 1094454077000, 175316619359, 6121173289, 0, 0] := by
  decide +kernel

theorem rows645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t645 = true := by
  decide +kernel

theorem tot645 : totK PA10K2 A10K2.t645 = [0, 276176619349, 1056179166898, 1654987076989, 1528716695854, 553545093146, 41240446447, 0, 0, 0] := by
  decide +kernel

theorem rows646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t646 = true := by
  decide +kernel

theorem tot646 : totK PA10K2 A10K2.t646 = [0, 281407675879, 1469038751976, 2143164486511, 748642101453, 52146068715, 0, 0, 0, 0] := by
  decide +kernel

theorem rows647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t647 = true := by
  decide +kernel

theorem tot647 : totK PA10K2 A10K2.t647 = [0, 214052912247, 776409989431, 1673668644622, 1573075080925, 414442546271, 30402056026, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
