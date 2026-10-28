import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6192 = true := by
  decide +kernel

theorem tot6192 : totK PD2M8K2 D2M8K2.t6192 = [0, 171151945050, 465948174865, 257412312407, 13869951582, 0, 0, 0] := by
  decide +kernel

theorem rows6193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6193 = true := by
  decide +kernel

theorem tot6193 : totK PD2M8K2 D2M8K2.t6193 = [0, 0, 286754488737, 488396988911, 116646932276, 1238673482, 0, 0] := by
  decide +kernel

theorem rows6194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6194 = true := by
  decide +kernel

theorem tot6194 : totK PD2M8K2 D2M8K2.t6194 = [90523122812, 139756494322, 138051740003, 347092835531, 160280825261, 8063697217, 0, 0] := by
  decide +kernel

theorem rows6195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6195 = true := by
  decide +kernel

theorem tot6195 : totK PD2M8K2 D2M8K2.t6195 = [154693690270, 466203999524, 252234605012, 15698772943, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
