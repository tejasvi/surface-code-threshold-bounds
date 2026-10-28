import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5928 = true := by
  decide +kernel

theorem tot5928 : totK PA10K2 A10K2.t5928 = [471804183793, 1811790236021, 1996181500283, 610123503813, 25317695645, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5929 = true := by
  decide +kernel

theorem tot5929 : totK PA10K2 A10K2.t5929 = [0, 507325939378, 1873939883438, 1894453487409, 497494261564, 25351274858, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5930 = true := by
  decide +kernel

theorem tot5930 : totK PA10K2 A10K2.t5930 = [512353472697, 1782390404297, 2002881576861, 797268794235, 91094952721, 5459593153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5931 = true := by
  decide +kernel

theorem tot5931 : totK PA10K2 A10K2.t5931 = [0, 876230857908, 2348587622612, 1633192905362, 300721566554, 19670719003, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
