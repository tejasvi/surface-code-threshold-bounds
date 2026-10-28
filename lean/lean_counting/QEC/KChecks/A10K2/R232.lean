import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t928 = true := by
  decide +kernel

theorem tot928 : totK PA10K2 A10K2.t928 = [0, 0, 530727346229, 1971062481740, 2010428191277, 442400120418, 13653259670, 0, 0, 0] := by
  decide +kernel

theorem rows929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t929 = true := by
  decide +kernel

theorem tot929 : totK PA10K2 A10K2.t929 = [0, 0, 585423975732, 1933828397677, 1853644677662, 570151742831, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t930 = true := by
  decide +kernel

theorem tot930 : totK PA10K2 A10K2.t930 = [0, 0, 466182780319, 1812609549278, 2051013313564, 567666408474, 18714921145, 0, 0, 0] := by
  decide +kernel

theorem rows931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t931 = true := by
  decide +kernel

theorem tot931 : totK PA10K2 A10K2.t931 = [0, 0, 0, 771035803565, 2262812591195, 1571622093214, 227175813901, 6318667960, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
