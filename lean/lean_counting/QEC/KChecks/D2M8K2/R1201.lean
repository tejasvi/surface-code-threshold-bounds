import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4804 = true := by
  decide +kernel

theorem tot4804 : totK PD2M8K2 D2M8K2.t4804 = [0, 60772201050, 327052676379, 414828629611, 96470129909, 1268739303, 0, 0] := by
  decide +kernel

theorem rows4805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4805 = true := by
  decide +kernel

theorem tot4805 : totK PD2M8K2 D2M8K2.t4805 = [0, 0, 219739878298, 485870419194, 173902702279, 7442000727, 0, 0] := by
  decide +kernel

theorem rows4806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4806 = true := by
  decide +kernel

theorem tot4806 : totK PD2M8K2 D2M8K2.t4806 = [0, 0, 180749835801, 469709036993, 218839042293, 14707859566, 0, 0] := by
  decide +kernel

theorem rows4807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4807 = true := by
  decide +kernel

theorem tot4807 : totK PD2M8K2 D2M8K2.t4807 = [0, 0, 201840034422, 486606975026, 197566600260, 7984731767, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
