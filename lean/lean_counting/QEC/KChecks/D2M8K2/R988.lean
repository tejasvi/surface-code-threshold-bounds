import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3952 = true := by
  decide +kernel

theorem tot3952 : totK PD2M8K2 D2M8K2.t3952 = [0, 0, 203869798689, 504318837759, 187514213904, 5296542560, 0, 0] := by
  decide +kernel

theorem rows3953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3953 = true := by
  decide +kernel

theorem tot3953 : totK PD2M8K2 D2M8K2.t3953 = [0, 173357259223, 390312505640, 234827988653, 96343278168, 6779302614, 0, 0] := by
  decide +kernel

theorem rows3954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3954 = true := by
  decide +kernel

theorem tot3954 : totK PD2M8K2 D2M8K2.t3954 = [0, 175597499564, 451013562124, 262207181882, 19434535327, 0, 0, 0] := by
  decide +kernel

theorem rows3955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3955 = true := by
  decide +kernel

theorem tot3955 : totK PD2M8K2 D2M8K2.t3955 = [0, 89098610365, 362969376858, 363590347021, 68761647047, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
