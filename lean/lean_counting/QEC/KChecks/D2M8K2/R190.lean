import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t760 = true := by
  decide +kernel

theorem tot760 : totK PD2M8K2 D2M8K2.t760 = [0, 181415877410, 464685927469, 234937134881, 14960490274, 0, 0, 0] := by
  decide +kernel

theorem rows761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t761 = true := by
  decide +kernel

theorem tot761 : totK PD2M8K2 D2M8K2.t761 = [0, 76502804610, 340935013708, 390351033138, 89798662467, 1369150432, 0, 0] := by
  decide +kernel

theorem rows762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t762 = true := by
  decide +kernel

theorem tot762 : totK PD2M8K2 D2M8K2.t762 = [0, 18616785608, 340319835552, 491359308267, 61819203752, 0, 0, 0] := by
  decide +kernel

theorem rows763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t763 = true := by
  decide +kernel

theorem tot763 : totK PD2M8K2 D2M8K2.t763 = [0, 202496408024, 479589775803, 204485275576, 9847636232, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
