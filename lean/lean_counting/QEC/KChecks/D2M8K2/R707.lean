import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2828 = true := by
  decide +kernel

theorem tot2828 : totK PD2M8K2 D2M8K2.t2828 = [0, 259213410980, 495598081965, 150920909204, 8417083954, 0, 0, 0] := by
  decide +kernel

theorem rows2829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2829 = true := by
  decide +kernel

theorem tot2829 : totK PD2M8K2 D2M8K2.t2829 = [90448200850, 325781774632, 394485085542, 101499539293, 3455941720, 0, 0, 0] := by
  decide +kernel

theorem rows2830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2830 = true := by
  decide +kernel

theorem tot2830 : totK PD2M8K2 D2M8K2.t2830 = [197144830566, 468711976153, 225217208965, 16686162190, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2831 = true := by
  decide +kernel

theorem tot2831 : totK PD2M8K2 D2M8K2.t2831 = [56284556089, 369509598862, 428008362511, 74819352007, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
