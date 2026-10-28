import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4308 = true := by
  decide +kernel

theorem tot4308 : totK PA10K2 A10K2.t4308 = [0, 0, 579900508809, 1881405928527, 1808617146342, 486795299530, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows4309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4309 = true := by
  decide +kernel

theorem tot4309 : totK PA10K2 A10K2.t4309 = [0, 0, 451036096487, 1820115026771, 2086177719436, 530523834995, 18676704670, 0, 0, 0] := by
  decide +kernel

theorem rows4310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4310 = true := by
  decide +kernel

theorem tot4310 : totK PA10K2 A10K2.t4310 = [0, 0, 507368612670, 1861075983084, 1866123943702, 447377823973, 25668410676, 0, 0, 0] := by
  decide +kernel

theorem rows4311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4311 = true := by
  decide +kernel

theorem tot4311 : totK PA10K2 A10K2.t4311 = [0, 0, 506999803652, 1896583625924, 1815466347702, 351235912100, 11323844185, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
