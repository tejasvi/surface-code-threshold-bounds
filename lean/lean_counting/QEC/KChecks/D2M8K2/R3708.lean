import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14832 = true := by
  decide +kernel

theorem tot14832 : totK PD2M8K2 D2M8K2.t14832 = [0, 163032137786, 448355909396, 264881077997, 24576434179, 0, 0, 0] := by
  decide +kernel

theorem rows14833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14833 = true := by
  decide +kernel

theorem tot14833 : totK PD2M8K2 D2M8K2.t14833 = [0, 159575551837, 465469538266, 255824809581, 13780374747, 0, 0, 0] := by
  decide +kernel

theorem rows14834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14834 = true := by
  decide +kernel

theorem tot14834 : totK PD2M8K2 D2M8K2.t14834 = [0, 0, 294081879896, 475699301299, 82252402661, 1021600638, 0, 0] := by
  decide +kernel

theorem rows14835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14835 = true := by
  decide +kernel

theorem tot14835 : totK PD2M8K2 D2M8K2.t14835 = [0, 173298171207, 395616503985, 240420886571, 69118110488, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
