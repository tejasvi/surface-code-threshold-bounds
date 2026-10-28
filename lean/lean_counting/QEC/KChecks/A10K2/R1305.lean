import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5220 = true := by
  decide +kernel

theorem tot5220 : totK PA10K2 A10K2.t5220 = [0, 0, 440261672059, 1762076934410, 1992279984572, 545431178947, 18905754890, 0, 0, 0] := by
  decide +kernel

theorem rows5221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5221 = true := by
  decide +kernel

theorem tot5221 : totK PA10K2 A10K2.t5221 = [0, 0, 0, 576490973544, 1969179726934, 1732059579340, 408993668264, 25371180993, 0, 0] := by
  decide +kernel

theorem rows5222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5222 = true := by
  decide +kernel

theorem tot5222 : totK PA10K2 A10K2.t5222 = [0, 0, 293535254566, 1272989556403, 1965756531701, 1091100820919, 178852896065, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5223 = true := by
  decide +kernel

theorem tot5223 : totK PA10K2 A10K2.t5223 = [0, 0, 432956676929, 1759845293142, 1895590427805, 499330051377, 32753171685, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
