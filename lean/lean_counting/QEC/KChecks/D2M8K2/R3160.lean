import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12640 = true := by
  decide +kernel

theorem tot12640 : totK PD2M8K2 D2M8K2.t12640 = [0, 0, 187149259026, 438902947909, 231290074852, 17104814242, 0, 0] := by
  decide +kernel

theorem rows12641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12641 = true := by
  decide +kernel

theorem tot12641 : totK PD2M8K2 D2M8K2.t12641 = [0, 0, 0, 319693395984, 473995407979, 78267254309, 1096505104, 0] := by
  decide +kernel

theorem rows12642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12642 = true := by
  decide +kernel

theorem tot12642 : totK PD2M8K2 D2M8K2.t12642 = [0, 0, 76346706397, 294765777038, 395736157011, 101380852570, 3838026431, 0] := by
  decide +kernel

theorem rows12643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12643 = true := by
  decide +kernel

theorem tot12643 : totK PD2M8K2 D2M8K2.t12643 = [0, 0, 195067825395, 477991473276, 210407361109, 6594457237, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
