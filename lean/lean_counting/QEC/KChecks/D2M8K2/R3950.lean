import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15800 = true := by
  decide +kernel

theorem tot15800 : totK PD2M8K2 D2M8K2.t15800 = [0, 0, 173056509801, 460403307110, 229128640076, 17638934824, 0, 0] := by
  decide +kernel

theorem rows15801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15801 = true := by
  decide +kernel

theorem tot15801 : totK PD2M8K2 D2M8K2.t15801 = [0, 0, 189201157998, 456803563854, 204205174788, 12206147664, 0, 0] := by
  decide +kernel

theorem rows15802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15802 = true := by
  decide +kernel

theorem tot15802 : totK PD2M8K2 D2M8K2.t15802 = [0, 0, 69446169779, 338703899044, 376709853113, 85960609371, 1369150432, 0] := by
  decide +kernel

theorem rows15803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15803 = true := by
  decide +kernel

theorem tot15803 : totK PD2M8K2 D2M8K2.t15803 = [0, 0, 51482212205, 364111350784, 396931439366, 46670854528, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
