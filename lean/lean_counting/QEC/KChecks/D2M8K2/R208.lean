import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t832 = true := by
  decide +kernel

theorem tot832 : totK PD2M8K2 D2M8K2.t832 = [0, 0, 173136865246, 474437256151, 231989881546, 19618532542, 0, 0] := by
  decide +kernel

theorem rows833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t833 = true := by
  decide +kernel

theorem tot833 : totK PD2M8K2 D2M8K2.t833 = [0, 0, 179076796195, 464537085105, 239118898962, 13960505070, 0, 0] := by
  decide +kernel

theorem rows834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t834 = true := by
  decide +kernel

theorem tot834 : totK PD2M8K2 D2M8K2.t834 = [0, 0, 87430099525, 341391894333, 365972088476, 79555356157, 1171084559, 0] := by
  decide +kernel

theorem rows835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t835 = true := by
  decide +kernel

theorem tot835 : totK PD2M8K2 D2M8K2.t835 = [0, 0, 0, 227794325046, 466700940138, 158437411944, 9444064503, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
