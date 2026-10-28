import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5032 = true := by
  decide +kernel

theorem tot5032 : totK PD2M8K2 D2M8K2.t5032 = [0, 0, 91298305516, 363478424692, 336574196234, 52858600626, 1021600638, 0] := by
  decide +kernel

theorem rows5033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5033 = true := by
  decide +kernel

theorem tot5033 : totK PD2M8K2 D2M8K2.t5033 = [0, 0, 0, 321681177503, 466162373858, 78257700701, 991020230, 0] := by
  decide +kernel

theorem rows5034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5034 = true := by
  decide +kernel

theorem tot5034 : totK PD2M8K2 D2M8K2.t5034 = [0, 0, 188081939077, 425444828986, 244415093031, 44708766153, 2561774784, 0] := by
  decide +kernel

theorem rows5035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5035 = true := by
  decide +kernel

theorem tot5035 : totK PD2M8K2 D2M8K2.t5035 = [0, 37944309145, 192843869027, 420699523782, 239705211491, 18057752351, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
