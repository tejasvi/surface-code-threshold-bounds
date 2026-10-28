import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4496 = true := by
  decide +kernel

theorem tot4496 : totK PD2M8K2 D2M8K2.t4496 = [0, 0, 217319070765, 484798415183, 203241797507, 11066126582, 0, 0] := by
  decide +kernel

theorem rows4497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4497 = true := by
  decide +kernel

theorem tot4497 : totK PD2M8K2 D2M8K2.t4497 = [0, 0, 170174465498, 467719806911, 229307901845, 13735475103, 0, 0] := by
  decide +kernel

theorem rows4498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4498 = true := by
  decide +kernel

theorem tot4498 : totK PD2M8K2 D2M8K2.t4498 = [0, 0, 176335119313, 472091540277, 235768200075, 15644178853, 0, 0] := by
  decide +kernel

theorem rows4499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4499 = true := by
  decide +kernel

theorem tot4499 : totK PD2M8K2 D2M8K2.t4499 = [0, 0, 174583700023, 464087823338, 230926168430, 16691388709, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
