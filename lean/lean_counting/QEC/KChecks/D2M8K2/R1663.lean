import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6652 = true := by
  decide +kernel

theorem tot6652 : totK PD2M8K2 D2M8K2.t6652 = [0, 176015966323, 454641315173, 240059550948, 16994558090, 0, 0, 0] := by
  decide +kernel

theorem rows6653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6653 = true := by
  decide +kernel

theorem tot6653 : totK PD2M8K2 D2M8K2.t6653 = [0, 0, 352656555122, 487908404868, 61772944847, 0, 0, 0] := by
  decide +kernel

theorem rows6654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6654 = true := by
  decide +kernel

theorem tot6654 : totK PD2M8K2 D2M8K2.t6654 = [0, 90138150790, 322259851924, 390602290303, 111952023346, 3880716147, 0, 0] := by
  decide +kernel

theorem rows6655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6655 = true := by
  decide +kernel

theorem tot6655 : totK PD2M8K2 D2M8K2.t6655 = [0, 153728888638, 448780940950, 290422116178, 23855774167, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
