import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3036 = true := by
  decide +kernel

theorem tot3036 : totK PD2M8K2 D2M8K2.t3036 = [0, 0, 92329175285, 411370489317, 343225407108, 33516219495, 0, 0] := by
  decide +kernel

theorem rows3037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3037 = true := by
  decide +kernel

theorem tot3037 : totK PD2M8K2 D2M8K2.t3037 = [0, 0, 241977855166, 491994640517, 165770745783, 6792782902, 0, 0] := by
  decide +kernel

theorem rows3038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3038 = true := by
  decide +kernel

theorem tot3038 : totK PD2M8K2 D2M8K2.t3038 = [0, 0, 190424658073, 480352708144, 204233539975, 10599746186, 0, 0] := by
  decide +kernel

theorem rows3039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3039 = true := by
  decide +kernel

theorem tot3039 : totK PD2M8K2 D2M8K2.t3039 = [0, 0, 178247437576, 450733843313, 254358903524, 23241079343, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
