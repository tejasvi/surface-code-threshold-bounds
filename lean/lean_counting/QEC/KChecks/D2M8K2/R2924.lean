import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11696 = true := by
  decide +kernel

theorem tot11696 : totK PD2M8K2 D2M8K2.t11696 = [0, 181014368181, 459440825971, 242237007593, 18660482440, 0, 0, 0] := by
  decide +kernel

theorem rows11697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11697 = true := by
  decide +kernel

theorem tot11697 : totK PD2M8K2 D2M8K2.t11697 = [0, 189297909047, 462457027495, 220327756724, 16702988424, 0, 0, 0] := by
  decide +kernel

theorem rows11698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11698 = true := by
  decide +kernel

theorem tot11698 : totK PD2M8K2 D2M8K2.t11698 = [0, 62982639912, 352304812069, 375266268117, 72198816001, 1095107716, 0, 0] := by
  decide +kernel

theorem rows11699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11699 = true := by
  decide +kernel

theorem tot11699 : totK PD2M8K2 D2M8K2.t11699 = [11364832707, 3901843494, 272769455283, 465350215629, 120016332161, 3882006667, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
