import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2372 = true := by
  decide +kernel

theorem tot2372 : totK PA10K2 A10K2.t2372 = [0, 0, 0, 518547573422, 1861144551057, 1832384954462, 485240062535, 31452573850, 0, 0] := by
  decide +kernel

theorem rows2373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2373 = true := by
  decide +kernel

theorem tot2373 : totK PA10K2 A10K2.t2373 = [0, 0, 466842231207, 1634289261309, 1794860893256, 704252211489, 75919056699, 0, 0, 0] := by
  decide +kernel

theorem rows2374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2374 = true := by
  decide +kernel

theorem tot2374 : totK PA10K2 A10K2.t2374 = [0, 0, 293526267267, 1503382475964, 2124171772582, 742870788241, 39496069575, 0, 0, 0] := by
  decide +kernel

theorem rows2375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2375 = true := by
  decide +kernel

theorem tot2375 : totK PA10K2 A10K2.t2375 = [0, 0, 298812713684, 1143338325487, 1854566877330, 1194098713146, 201651015737, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
