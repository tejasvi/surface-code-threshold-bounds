import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3928 = true := by
  decide +kernel

theorem tot3928 : totK PD2M8K2 D2M8K2.t3928 = [0, 146296601270, 371979549772, 284416022072, 73226409737, 3720136285, 0, 0] := by
  decide +kernel

theorem rows3929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3929 = true := by
  decide +kernel

theorem tot3929 : totK PD2M8K2 D2M8K2.t3929 = [0, 164751240600, 443363809784, 277353407464, 29796576154, 0, 0, 0] := by
  decide +kernel

theorem rows3930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3930 = true := by
  decide +kernel

theorem tot3930 : totK PD2M8K2 D2M8K2.t3930 = [0, 111868955890, 422683152472, 340158265736, 28717747649, 0, 0, 0] := by
  decide +kernel

theorem rows3931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3931 = true := by
  decide +kernel

theorem tot3931 : totK PD2M8K2 D2M8K2.t3931 = [0, 0, 211114102993, 490895045481, 177711071468, 4967996017, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
