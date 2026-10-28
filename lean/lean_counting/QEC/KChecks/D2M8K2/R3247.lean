import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12988 = true := by
  decide +kernel

theorem tot12988 : totK PD2M8K2 D2M8K2.t12988 = [0, 0, 180767685019, 464943192691, 238157971230, 12489878387, 0, 0] := by
  decide +kernel

theorem rows12989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12989 = true := by
  decide +kernel

theorem tot12989 : totK PD2M8K2 D2M8K2.t12989 = [0, 145194857232, 361434774118, 274064422585, 115818822751, 9161262273, 0, 0] := by
  decide +kernel

theorem rows12990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12990 = true := by
  decide +kernel

theorem tot12990 : totK PD2M8K2 D2M8K2.t12990 = [0, 188777631506, 449572270874, 227852258446, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows12991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12991 = true := by
  decide +kernel

theorem tot12991 : totK PD2M8K2 D2M8K2.t12991 = [0, 69361752376, 359385792324, 364776472265, 71863563141, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
