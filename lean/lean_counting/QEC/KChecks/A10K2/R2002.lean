import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8008 = true := by
  decide +kernel

theorem tot8008 : totK PA10K2 A10K2.t8008 = [0, 0, 514425452703, 1785048469668, 1829989736929, 582438269885, 113270062929, 6356241174, 0, 0] := by
  decide +kernel

theorem rows8009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8009 = true := by
  decide +kernel

theorem tot8009 : totK PA10K2 A10K2.t8009 = [0, 0, 263410905076, 1411343772602, 2201050069394, 1055181447171, 100489474204, 0, 0, 0] := by
  decide +kernel

theorem rows8010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8010 = true := by
  decide +kernel

theorem tot8010 : totK PA10K2 A10K2.t8010 = [0, 0, 111865401186, 742749959223, 1830850256607, 1672613950666, 433559088403, 18457393337, 0, 0] := by
  decide +kernel

theorem rows8011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8011 = true := by
  decide +kernel

theorem tot8011 : totK PA10K2 A10K2.t8011 = [0, 0, 479000178303, 1863848404505, 2101693563165, 626521625753, 26321530115, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
