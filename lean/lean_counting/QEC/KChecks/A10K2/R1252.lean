import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5008 = true := by
  decide +kernel

theorem tot5008 : totK PA10K2 A10K2.t5008 = [0, 257947951571, 1453067830097, 2130032198196, 811128227722, 60488583098, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5009 = true := by
  decide +kernel

theorem tot5009 : totK PA10K2 A10K2.t5009 = [0, 0, 472479404308, 1815699098744, 1861628494274, 489010548393, 30818366867, 0, 0, 0] := by
  decide +kernel

theorem rows5010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5010 = true := by
  decide +kernel

theorem tot5010 : totK PA10K2 A10K2.t5010 = [0, 487592432303, 1751465874757, 1843386754204, 612929384751, 49442850814, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5011 = true := by
  decide +kernel

theorem tot5011 : totK PA10K2 A10K2.t5011 = [0, 296762186447, 1486795910187, 2116667756086, 796373962971, 58994932240, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
