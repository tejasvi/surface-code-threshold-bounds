import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6092 = true := by
  decide +kernel

theorem tot6092 : totK PA10K2 A10K2.t6092 = [0, 476997066642, 1862154154664, 2044232554157, 550978558877, 18893391764, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6093 = true := by
  decide +kernel

theorem tot6093 : totK PA10K2 A10K2.t6093 = [0, 0, 563858630444, 1970844456697, 1819263109623, 393521803790, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows6094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6094 = true := by
  decide +kernel

theorem tot6094 : totK PA10K2 A10K2.t6094 = [0, 378391818490, 1605604435361, 2126136804636, 886147278170, 84732997885, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6095 = true := by
  decide +kernel

theorem tot6095 : totK PA10K2 A10K2.t6095 = [0, 306990390918, 1445777100805, 2201623876273, 1069111031919, 105341377880, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
