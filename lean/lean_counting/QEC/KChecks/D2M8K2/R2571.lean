import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10284 = true := by
  decide +kernel

theorem tot10284 : totK PD2M8K2 D2M8K2.t10284 = [0, 0, 208555975914, 508212345703, 166253008109, 2519015093, 0, 0] := by
  decide +kernel

theorem rows10285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10285 = true := by
  decide +kernel

theorem tot10285 : totK PD2M8K2 D2M8K2.t10285 = [0, 0, 170711992347, 462498718797, 236243546004, 13621712409, 0, 0] := by
  decide +kernel

theorem rows10286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10286 = true := by
  decide +kernel

theorem tot10286 : totK PD2M8K2 D2M8K2.t10286 = [0, 0, 0, 295525468726, 471475402810, 86640411408, 1239866073, 0] := by
  decide +kernel

theorem rows10287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10287 = true := by
  decide +kernel

theorem tot10287 : totK PD2M8K2 D2M8K2.t10287 = [0, 0, 93173791751, 392777031329, 380543557835, 42088959888, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
