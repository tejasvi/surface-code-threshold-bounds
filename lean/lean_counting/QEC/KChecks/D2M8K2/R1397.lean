import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5588 = true := by
  decide +kernel

theorem tot5588 : totK PD2M8K2 D2M8K2.t5588 = [0, 216979670591, 488104290186, 180954975615, 4965269624, 0, 0, 0] := by
  decide +kernel

theorem rows5589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5589 = true := by
  decide +kernel

theorem tot5589 : totK PD2M8K2 D2M8K2.t5589 = [0, 190038553939, 460051463525, 217428387163, 17076867616, 0, 0, 0] := by
  decide +kernel

theorem rows5590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5590 = true := by
  decide +kernel

theorem tot5590 : totK PD2M8K2 D2M8K2.t5590 = [0, 158471412375, 483988982800, 234226309859, 9604240528, 0, 0, 0] := by
  decide +kernel

theorem rows5591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5591 = true := by
  decide +kernel

theorem tot5591 : totK PD2M8K2 D2M8K2.t5591 = [0, 169887002527, 466165552880, 226905543359, 14140236668, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
