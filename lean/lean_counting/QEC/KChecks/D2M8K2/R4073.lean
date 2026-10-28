import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16292 = true := by
  decide +kernel

theorem tot16292 : totK PD2M8K2 D2M8K2.t16292 = [0, 0, 174718340841, 395164841849, 251512621964, 83301001992, 4246544562, 0] := by
  decide +kernel

theorem rows16293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16293 = true := by
  decide +kernel

theorem tot16293 : totK PD2M8K2 D2M8K2.t16293 = [0, 0, 175246914687, 433111057470, 277090028809, 29591424931, 0, 0] := by
  decide +kernel

theorem rows16294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16294 = true := by
  decide +kernel

theorem tot16294 : totK PD2M8K2 D2M8K2.t16294 = [0, 0, 89076128973, 403596653311, 348942490412, 49010043595, 1164319620, 0] := by
  decide +kernel

theorem rows16295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16295 = true := by
  decide +kernel

theorem tot16295 : totK PD2M8K2 D2M8K2.t16295 = [0, 0, 0, 233923079037, 503611793573, 153498474247, 6670298691, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
