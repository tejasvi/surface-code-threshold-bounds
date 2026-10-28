import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6784 = true := by
  decide +kernel

theorem tot6784 : totK PA10K2 A10K2.t6784 = [460648103006, 1469395384655, 1429835770504, 576972344038, 533778803566, 337104436601, 43287591117, 0, 0, 0] := by
  decide +kernel

theorem rows6785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6785 = true := by
  decide +kernel

theorem tot6785 : totK PA10K2 A10K2.t6785 = [346772101404, 1591619859037, 2067121066528, 809276501308, 72529193930, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6786 = true := by
  decide +kernel

theorem tot6786 : totK PA10K2 A10K2.t6786 = [0, 500577921421, 1774135368513, 1733159192279, 470330153761, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6787 = true := by
  decide +kernel

theorem tot6787 : totK PA10K2 A10K2.t6787 = [441487391689, 1622001397783, 1904086905009, 814123085621, 85992672972, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
