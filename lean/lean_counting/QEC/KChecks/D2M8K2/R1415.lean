import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5660 = true := by
  decide +kernel

theorem tot5660 : totK PD2M8K2 D2M8K2.t5660 = [0, 187280952160, 463745224897, 252153514161, 17901712418, 0, 0, 0] := by
  decide +kernel

theorem rows5661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5661 = true := by
  decide +kernel

theorem tot5661 : totK PD2M8K2 D2M8K2.t5661 = [0, 190871845179, 471057191027, 224073193186, 14815639298, 0, 0, 0] := by
  decide +kernel

theorem rows5662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5662 = true := by
  decide +kernel

theorem tot5662 : totK PD2M8K2 D2M8K2.t5662 = [0, 174179658447, 442137801380, 265967954723, 27787646201, 0, 0, 0] := by
  decide +kernel

theorem rows5663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5663 = true := by
  decide +kernel

theorem tot5663 : totK PD2M8K2 D2M8K2.t5663 = [0, 99586626754, 400151365390, 339872732909, 41993552504, 1075657031, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
