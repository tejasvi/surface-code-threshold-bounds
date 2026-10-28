import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6760 = true := by
  decide +kernel

theorem tot6760 : totK PD2M8K2 D2M8K2.t6760 = [4194847968, 262957851455, 440901367418, 194447141035, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows6761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6761 = true := by
  decide +kernel

theorem tot6761 : totK PD2M8K2 D2M8K2.t6761 = [0, 198877398829, 483063153364, 201216040709, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows6762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6762 = true := by
  decide +kernel

theorem tot6762 : totK PD2M8K2 D2M8K2.t6762 = [79906847188, 268289601313, 369302777372, 174016848098, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows6763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6763 = true := by
  decide +kernel

theorem tot6763 : totK PD2M8K2 D2M8K2.t6763 = [169819598880, 444561802644, 278293589994, 30470443108, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
