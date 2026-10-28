import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5960 = true := by
  decide +kernel

theorem tot5960 : totK PD2M8K2 D2M8K2.t5960 = [0, 191914153703, 470566282636, 221405579124, 12305796314, 0, 0, 0] := by
  decide +kernel

theorem rows5961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5961 = true := by
  decide +kernel

theorem tot5961 : totK PD2M8K2 D2M8K2.t5961 = [0, 0, 301850763022, 507771644615, 94497432733, 0, 0, 0] := by
  decide +kernel

theorem rows5962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5962 = true := by
  decide +kernel

theorem tot5962 : totK PD2M8K2 D2M8K2.t5962 = [0, 0, 204994913449, 472675734534, 180991415315, 8706415949, 0, 0] := by
  decide +kernel

theorem rows5963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5963 = true := by
  decide +kernel

theorem tot5963 : totK PD2M8K2 D2M8K2.t5963 = [0, 203826198170, 455303148680, 237601146334, 27919482091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
