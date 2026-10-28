import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9120 = true := by
  decide +kernel

theorem tot9120 : totK PD2M8K2 D2M8K2.t9120 = [0, 0, 213216449862, 497985177084, 146996098481, 2430600193, 0, 0] := by
  decide +kernel

theorem rows9121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9121 = true := by
  decide +kernel

theorem tot9121 : totK PD2M8K2 D2M8K2.t9121 = [0, 0, 169166523964, 457571347757, 218307474853, 13516151468, 0, 0] := by
  decide +kernel

theorem rows9122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9122 = true := by
  decide +kernel

theorem tot9122 : totK PD2M8K2 D2M8K2.t9122 = [0, 0, 0, 322161631438, 433724604280, 62537161791, 1138244013, 0] := by
  decide +kernel

theorem rows9123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9123 = true := by
  decide +kernel

theorem tot9123 : totK PD2M8K2 D2M8K2.t9123 = [0, 0, 190613287615, 450208836723, 238440808502, 18738721289, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
