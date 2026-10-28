import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11652 = true := by
  decide +kernel

theorem tot11652 : totK PD2M8K2 D2M8K2.t11652 = [0, 84248551590, 357479421798, 350693641224, 63324822638, 1206465782, 0, 0] := by
  decide +kernel

theorem rows11653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11653 = true := by
  decide +kernel

theorem tot11653 : totK PD2M8K2 D2M8K2.t11653 = [0, 38598824603, 366043660103, 429079900904, 43316249299, 0, 0, 0] := by
  decide +kernel

theorem rows11654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11654 = true := by
  decide +kernel

theorem tot11654 : totK PD2M8K2 D2M8K2.t11654 = [0, 174699428591, 450411318264, 271095139101, 29184232052, 0, 0, 0] := by
  decide +kernel

theorem rows11655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11655 = true := by
  decide +kernel

theorem tot11655 : totK PD2M8K2 D2M8K2.t11655 = [0, 208790356353, 492412970654, 186807745485, 6915473937, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
