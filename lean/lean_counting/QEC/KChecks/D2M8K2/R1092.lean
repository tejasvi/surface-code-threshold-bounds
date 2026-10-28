import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4368 = true := by
  decide +kernel

theorem tot4368 : totK PD2M8K2 D2M8K2.t4368 = [0, 94118362629, 417393737603, 346371742977, 34149556870, 0, 0, 0] := by
  decide +kernel

theorem rows4369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4369 = true := by
  decide +kernel

theorem tot4369 : totK PD2M8K2 D2M8K2.t4369 = [0, 0, 277051151472, 512369131628, 107676709773, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4370 = true := by
  decide +kernel

theorem tot4370 : totK PD2M8K2 D2M8K2.t4370 = [0, 160216744043, 445886534223, 281226121674, 28481470311, 0, 0, 0] := by
  decide +kernel

theorem rows4371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4371 = true := by
  decide +kernel

theorem tot4371 : totK PD2M8K2 D2M8K2.t4371 = [0, 177415509518, 458767595882, 241147904869, 14740892251, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
