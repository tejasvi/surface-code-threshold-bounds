import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4460 = true := by
  decide +kernel

theorem tot4460 : totK PA10K2 A10K2.t4460 = [0, 548577217461, 1922998265073, 1897839472401, 456145844684, 12917769548, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4461 = true := by
  decide +kernel

theorem tot4461 : totK PA10K2 A10K2.t4461 = [0, 0, 655271483456, 2010250168815, 1621725654958, 391413943146, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows4462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4462 = true := by
  decide +kernel

theorem tot4462 : totK PA10K2 A10K2.t4462 = [0, 365777074080, 1319159676664, 1769277796316, 1060711088312, 178995699509, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows4463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4463 = true := by
  decide +kernel

theorem tot4463 : totK PA10K2 A10K2.t4463 = [0, 361708485942, 1650291179637, 2057896758960, 610580120264, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
