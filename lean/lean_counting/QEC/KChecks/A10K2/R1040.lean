import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4160 = true := by
  decide +kernel

theorem tot4160 : totK PA10K2 A10K2.t4160 = [0, 732913356586, 2056666734377, 1576805811040, 374340748030, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4161 = true := by
  decide +kernel

theorem tot4161 : totK PA10K2 A10K2.t4161 = [288483183456, 1098080088254, 1811260892847, 1284332301024, 211454659097, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4162 = true := by
  decide +kernel

theorem tot4162 : totK PA10K2 A10K2.t4162 = [481540779949, 1676753714739, 1906319458616, 657115145511, 52230035883, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4163 = true := by
  decide +kernel

theorem tot4163 : totK PA10K2 A10K2.t4163 = [0, 1057067872430, 2405845165463, 1174989036177, 107172403957, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
