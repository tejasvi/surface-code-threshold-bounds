import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5744 = true := by
  decide +kernel

theorem tot5744 : totK PA10K2 A10K2.t5744 = [0, 0, 489555400315, 1823879748208, 1902897520886, 515803267199, 18560348465, 0, 0, 0] := by
  decide +kernel

theorem rows5745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5745 = true := by
  decide +kernel

theorem tot5745 : totK PA10K2 A10K2.t5745 = [0, 0, 0, 626278130923, 2018065707934, 1599420453274, 345897599647, 25371180993, 0, 0] := by
  decide +kernel

theorem rows5746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5746 = true := by
  decide +kernel

theorem tot5746 : totK PA10K2 A10K2.t5746 = [0, 0, 285008661260, 1240074966957, 1884652650794, 1078763347819, 176205478641, 5447185874, 0, 0] := by
  decide +kernel

theorem rows5747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5747 = true := by
  decide +kernel

theorem tot5747 : totK PA10K2 A10K2.t5747 = [0, 0, 499345957490, 1820148063679, 1890348152752, 525765893442, 32110382941, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
