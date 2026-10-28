import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5896 = true := by
  decide +kernel

theorem tot5896 : totK PD2M8K2 D2M8K2.t5896 = [177780646283, 454274947708, 257567207072, 24434903335, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5897 = true := by
  decide +kernel

theorem tot5897 : totK PD2M8K2 D2M8K2.t5897 = [142182942151, 446683486002, 288045032292, 23236460081, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5898 = true := by
  decide +kernel

theorem tot5898 : totK PD2M8K2 D2M8K2.t5898 = [0, 207761476613, 475601288020, 183223555463, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows5899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5899 = true := by
  decide +kernel

theorem tot5899 : totK PD2M8K2 D2M8K2.t5899 = [81042165927, 328011019202, 365370112200, 100147299518, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
