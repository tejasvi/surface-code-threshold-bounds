import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t160 = true := by
  decide +kernel

theorem tot160 : totK PD2M8K2 D2M8K2.t160 = [0, 55018178737, 361563095180, 438502431546, 42556811976, 0, 0, 0] := by
  decide +kernel

theorem rows161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t161 = true := by
  decide +kernel

theorem tot161 : totK PD2M8K2 D2M8K2.t161 = [0, 181188582821, 446871975683, 255024532694, 26880988181, 0, 0, 0] := by
  decide +kernel

theorem rows162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t162 = true := by
  decide +kernel

theorem tot162 : totK PD2M8K2 D2M8K2.t162 = [0, 173916283009, 455967982319, 253852983237, 20170069073, 0, 0, 0] := by
  decide +kernel

theorem rows163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t163 = true := by
  decide +kernel

theorem tot163 : totK PD2M8K2 D2M8K2.t163 = [0, 170375439666, 453926505815, 257038621913, 21639026309, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
