import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1896 = true := by
  decide +kernel

theorem tot1896 : totK PA10K2 A10K2.t1896 = [0, 562204777993, 1902588997386, 1795671443704, 573764563145, 59585918262, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1897 = true := by
  decide +kernel

theorem tot1897 : totK PA10K2 A10K2.t1897 = [0, 80160914684, 879202502746, 2171249963425, 1383608904458, 198701217078, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1898 = true := by
  decide +kernel

theorem tot1898 : totK PA10K2 A10K2.t1898 = [0, 549642715264, 1934116693616, 1991839282914, 569782609225, 38818003701, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1899 = true := by
  decide +kernel

theorem tot1899 : totK PA10K2 A10K2.t1899 = [0, 162737985116, 1145355730812, 2170846157380, 1397367457713, 259279815494, 6840736825, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
