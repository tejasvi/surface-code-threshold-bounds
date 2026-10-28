import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6020 = true := by
  decide +kernel

theorem tot6020 : totK PD2M8K2 D2M8K2.t6020 = [0, 0, 179033216875, 466291747678, 238067161027, 13761953177, 0, 0] := by
  decide +kernel

theorem rows6021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6021 = true := by
  decide +kernel

theorem tot6021 : totK PD2M8K2 D2M8K2.t6021 = [0, 0, 86585668253, 402162400468, 361695750240, 35844985901, 0, 0] := by
  decide +kernel

theorem rows6022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6022 = true := by
  decide +kernel

theorem tot6022 : totK PD2M8K2 D2M8K2.t6022 = [0, 0, 0, 211052649083, 483837186947, 157704164617, 5320761635, 0] := by
  decide +kernel

theorem rows6023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6023 = true := by
  decide +kernel

theorem tot6023 : totK PD2M8K2 D2M8K2.t6023 = [0, 0, 181444095191, 465110575475, 231431960654, 16131077680, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
