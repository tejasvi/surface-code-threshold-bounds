import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4184 = true := by
  decide +kernel

theorem tot4184 : totK PD2M8K2 D2M8K2.t4184 = [0, 0, 180890915328, 492142355711, 242671629815, 8792955130, 0, 0] := by
  decide +kernel

theorem rows4185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4185 = true := by
  decide +kernel

theorem tot4185 : totK PD2M8K2 D2M8K2.t4185 = [0, 0, 164838283716, 445174533986, 265820737604, 27474544470, 0, 0] := by
  decide +kernel

theorem rows4186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4186 = true := by
  decide +kernel

theorem tot4186 : totK PD2M8K2 D2M8K2.t4186 = [0, 0, 190824410366, 457449503323, 226249715191, 16181423383, 0, 0] := by
  decide +kernel

theorem rows4187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4187 = true := by
  decide +kernel

theorem tot4187 : totK PD2M8K2 D2M8K2.t4187 = [0, 0, 53165745754, 371349217741, 426197284237, 54416962819, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
