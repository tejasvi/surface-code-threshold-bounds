import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t824 = true := by
  decide +kernel

theorem tot824 : totK PA10K2 A10K2.t824 = [0, 304795442860, 1568007899883, 2161068905553, 880537938326, 77221379080, 0, 0, 0, 0] := by
  decide +kernel

theorem rows825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t825 = true := by
  decide +kernel

theorem tot825 : totK PA10K2 A10K2.t825 = [0, 139103737231, 925735969154, 2054401629478, 1505597797987, 262910779263, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t826 = true := by
  decide +kernel

theorem tot826 : totK PA10K2 A10K2.t826 = [0, 499773104138, 1864292306085, 2033128867942, 598195237733, 23581264317, 0, 0, 0, 0] := by
  decide +kernel

theorem rows827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t827 = true := by
  decide +kernel

theorem tot827 : totK PA10K2 A10K2.t827 = [0, 227359472010, 1233813769461, 2099722112123, 1213237071411, 180707278111, 6066958478, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
