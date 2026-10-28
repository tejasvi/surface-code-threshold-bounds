import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t896 = true := by
  decide +kernel

theorem tot896 : totK PD2M8K2 D2M8K2.t896 = [51598200566, 352084078677, 453508103465, 58934045244, 0, 0, 0, 0] := by
  decide +kernel

theorem rows897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t897 = true := by
  decide +kernel

theorem tot897 : totK PD2M8K2 D2M8K2.t897 = [190957519133, 468018579513, 227454190749, 18524742043, 0, 0, 0, 0] := by
  decide +kernel

theorem rows898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t898 = true := by
  decide +kernel

theorem tot898 : totK PD2M8K2 D2M8K2.t898 = [165571498313, 462149880055, 247805925815, 13632511348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t899 = true := by
  decide +kernel

theorem tot899 : totK PD2M8K2 D2M8K2.t899 = [0, 279767892071, 502823243844, 110669481202, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
