import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9932 = true := by
  decide +kernel

theorem tot9932 : totK PD2M8K2 D2M8K2.t9932 = [0, 0, 186603815009, 443691366968, 248896110969, 18682401836, 0, 0] := by
  decide +kernel

theorem rows9933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9933 = true := by
  decide +kernel

theorem tot9933 : totK PD2M8K2 D2M8K2.t9933 = [0, 0, 125648786292, 434207141363, 302966905258, 23155246752, 0, 0] := by
  decide +kernel

theorem rows9934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9934 = true := by
  decide +kernel

theorem tot9934 : totK PD2M8K2 D2M8K2.t9934 = [0, 0, 0, 205835932079, 489509853147, 168166507800, 9548758518, 0] := by
  decide +kernel

theorem rows9935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9935 = true := by
  decide +kernel

theorem tot9935 : totK PD2M8K2 D2M8K2.t9935 = [0, 0, 87770539582, 329068122367, 364333157854, 85613457173, 3543621287, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
