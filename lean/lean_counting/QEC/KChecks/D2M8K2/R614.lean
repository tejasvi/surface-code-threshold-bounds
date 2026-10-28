import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2456 = true := by
  decide +kernel

theorem tot2456 : totK PD2M8K2 D2M8K2.t2456 = [0, 233874531076, 499566659386, 158492482294, 4777701754, 0, 0, 0] := by
  decide +kernel

theorem rows2457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2457 = true := by
  decide +kernel

theorem tot2457 : totK PD2M8K2 D2M8K2.t2457 = [0, 178779249288, 475720096415, 218650487363, 9951072380, 0, 0, 0] := by
  decide +kernel

theorem rows2458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2458 = true := by
  decide +kernel

theorem tot2458 : totK PD2M8K2 D2M8K2.t2458 = [0, 182735830479, 447459723386, 273638921922, 32229084478, 0, 0, 0] := by
  decide +kernel

theorem rows2459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2459 = true := by
  decide +kernel

theorem tot2459 : totK PD2M8K2 D2M8K2.t2459 = [0, 182866893873, 475936350956, 240679235699, 11019007305, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
