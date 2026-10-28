import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12696 = true := by
  decide +kernel

theorem tot12696 : totK PD2M8K2 D2M8K2.t12696 = [0, 0, 0, 205909816334, 469127073488, 171028563202, 11819130176, 0] := by
  decide +kernel

theorem rows12697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12697 = true := by
  decide +kernel

theorem tot12697 : totK PD2M8K2 D2M8K2.t12697 = [0, 0, 185648347603, 464057337104, 235826682741, 15507985299, 0, 0] := by
  decide +kernel

theorem rows12698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12698 = true := by
  decide +kernel

theorem tot12698 : totK PD2M8K2 D2M8K2.t12698 = [0, 0, 199268401571, 465964348143, 222605988159, 12523541424, 0, 0] := by
  decide +kernel

theorem rows12699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12699 = true := by
  decide +kernel

theorem tot12699 : totK PD2M8K2 D2M8K2.t12699 = [0, 0, 19975053532, 311255802472, 460635227470, 85356888989, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
