import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2448 = true := by
  decide +kernel

theorem tot2448 : totK PD2M8K2 D2M8K2.t2448 = [0, 215384145453, 488133821188, 182096095400, 9509098305, 0, 0, 0] := by
  decide +kernel

theorem rows2449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2449 = true := by
  decide +kernel

theorem tot2449 : totK PD2M8K2 D2M8K2.t2449 = [65979365819, 304445665604, 394464223561, 107531701886, 3554346603, 0, 0, 0] := by
  decide +kernel

theorem rows2450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2450 = true := by
  decide +kernel

theorem tot2450 : totK PD2M8K2 D2M8K2.t2450 = [176680345251, 456097495582, 268211217038, 26594259117, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2451 = true := by
  decide +kernel

theorem tot2451 : totK PD2M8K2 D2M8K2.t2451 = [177709164412, 474928594560, 234589401165, 12096604323, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
