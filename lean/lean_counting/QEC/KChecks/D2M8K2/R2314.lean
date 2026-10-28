import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9256 = true := by
  decide +kernel

theorem tot9256 : totK PD2M8K2 D2M8K2.t9256 = [92968305029, 384160655225, 397201909995, 50203716004, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9257 = true := by
  decide +kernel

theorem tot9257 : totK PD2M8K2 D2M8K2.t9257 = [190379380629, 458797420262, 242415696856, 19913872922, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9258 = true := by
  decide +kernel

theorem tot9258 : totK PD2M8K2 D2M8K2.t9258 = [135217399024, 437035067335, 306008404831, 35029272160, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9259 = true := by
  decide +kernel

theorem tot9259 : totK PD2M8K2 D2M8K2.t9259 = [0, 186854962536, 441456356149, 251783582045, 25353971821, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
