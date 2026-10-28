import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13332 = true := by
  decide +kernel

theorem tot13332 : totK PD2M8K2 D2M8K2.t13332 = [0, 96572542650, 342975873731, 348849537776, 93308860443, 3581949829, 0, 0] := by
  decide +kernel

theorem rows13333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13333 = true := by
  decide +kernel

theorem tot13333 : totK PD2M8K2 D2M8K2.t13333 = [0, 172576997065, 437040612145, 267478212402, 30240056193, 0, 0, 0] := by
  decide +kernel

theorem rows13334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13334 = true := by
  decide +kernel

theorem tot13334 : totK PD2M8K2 D2M8K2.t13334 = [0, 148141543280, 464136944886, 274746663624, 18713532954, 0, 0, 0] := by
  decide +kernel

theorem rows13335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13335 = true := by
  decide +kernel

theorem tot13335 : totK PD2M8K2 D2M8K2.t13335 = [0, 0, 285141473604, 518242982125, 102901211941, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
