import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A7

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows2815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2815 = true := by
  rw [show A10K2.u2815 = KTree.node A10K2.u2813 (nat_lit 46749171) (nat_lit 9005427068) (nat_lit 0) A10K2.u2814 from rfl, allE_node, arows2813, irow2815, arows2814]
  all_goals rfl

theorem atot2815 : totK PA10K2 A10K2.u2815 = [1443757010989, 6077359818761, 8177731964868, 3537597919082, 400513590309, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u2815 = KTree.node A10K2.u2813 (nat_lit 46749171) (nat_lit 9005427068) (nat_lit 0) A10K2.u2814 from rfl, totK_node, atot2813, atot2814]
  decide +kernel

theorem arows2818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2818 = true := by
  rw [show A10K2.u2818 = KTree.node A10K2.u2816 (nat_lit 46769607) (nat_lit 13781658112) (nat_lit 0) A10K2.u2817 from rfl, allE_node, arows2816, irow2818, arows2817]
  all_goals rfl

theorem atot2818 : totK PA10K2 A10K2.u2818 = [0, 1777245851665, 6696475978122, 7799719541370, 3022217885060, 442805231478, 20331139758, 0, 0, 0] := by
  rw [show A10K2.u2818 = KTree.node A10K2.u2816 (nat_lit 46769607) (nat_lit 13781658112) (nat_lit 0) A10K2.u2817 from rfl, totK_node, atot2816, atot2817]
  decide +kernel

theorem arows2822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2822 = true := by
  rw [show A10K2.u2822 = KTree.node A10K2.u2820 (nat_lit 46779156) (nat_lit 13293080596) (nat_lit 0) A10K2.u2821 from rfl, allE_node, arows2820, irow2822, arows2821]
  all_goals rfl

theorem atot2822 : totK PA10K2 A10K2.u2822 = [0, 1215297620829, 5485168004221, 8040958291378, 3920229617853, 503103586272, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u2822 = KTree.node A10K2.u2820 (nat_lit 46779156) (nat_lit 13293080596) (nat_lit 0) A10K2.u2821 from rfl, totK_node, atot2820, atot2821]
  decide +kernel

theorem arows2825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2825 = true := by
  rw [show A10K2.u2825 = KTree.node A10K2.u2823 (nat_lit 46804644) (nat_lit 12647938791) (nat_lit 0) A10K2.u2824 from rfl, allE_node, arows2823, irow2825, arows2824]
  all_goals rfl

theorem atot2825 : totK PA10K2 A10K2.u2825 = [1079427622363, 4769975380894, 7585359451593, 5059958973724, 1234247465186, 82268358908, 0, 0, 0, 0] := by
  rw [show A10K2.u2825 = KTree.node A10K2.u2823 (nat_lit 46804644) (nat_lit 12647938791) (nat_lit 0) A10K2.u2824 from rfl, totK_node, atot2823, atot2824]
  decide +kernel

theorem arows2830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2830 = true := by
  rw [show A10K2.u2830 = KTree.node A10K2.u2828 (nat_lit 46816022) (nat_lit 5727583772) (nat_lit 0) A10K2.u2829 from rfl, allE_node, arows2828, irow2830, arows2829]
  all_goals rfl

theorem atot2830 : totK PA10K2 A10K2.u2830 = [459144823843, 3597041039697, 7872729287449, 5978058385048, 1364408703511, 70432589585, 0, 0, 0, 0] := by
  rw [show A10K2.u2830 = KTree.node A10K2.u2828 (nat_lit 46816022) (nat_lit 5727583772) (nat_lit 0) A10K2.u2829 from rfl, totK_node, atot2828, atot2829]
  decide +kernel

theorem arows2833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2833 = true := by
  rw [show A10K2.u2833 = KTree.node A10K2.u2831 (nat_lit 46848787) (nat_lit 9976155606) (nat_lit 0) A10K2.u2832 from rfl, allE_node, arows2831, irow2833, arows2832]
  all_goals rfl

theorem atot2833 : totK PA10K2 A10K2.u2833 = [556621861187, 3127895273103, 6681526225756, 6262248238277, 2301691110830, 310770144537, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2833 = KTree.node A10K2.u2831 (nat_lit 46848787) (nat_lit 9976155606) (nat_lit 0) A10K2.u2832 from rfl, totK_node, atot2831, atot2832]
  decide +kernel

theorem arows2837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2837 = true := by
  rw [show A10K2.u2837 = KTree.node A10K2.u2835 (nat_lit 46872018) (nat_lit 15449247974) (nat_lit 0) A10K2.u2836 from rfl, allE_node, arows2835, irow2837, arows2836]
  all_goals rfl

theorem atot2837 : totK PA10K2 A10K2.u2837 = [1338933740180, 5604907722117, 7930987211780, 4224420572403, 723511324442, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u2837 = KTree.node A10K2.u2835 (nat_lit 46872018) (nat_lit 15449247974) (nat_lit 0) A10K2.u2836 from rfl, totK_node, atot2835, atot2836]
  decide +kernel

theorem arows2840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2840 = true := by
  rw [show A10K2.u2840 = KTree.node A10K2.u2838 (nat_lit 46890231) (nat_lit 14693586544) (nat_lit 0) A10K2.u2839 from rfl, allE_node, arows2838, irow2840, arows2839]
  all_goals rfl

theorem atot2840 : totK PA10K2 A10K2.u2840 = [327742824672, 2732837193793, 7080111288755, 7116931274330, 2490839332552, 222896424211, 0, 0, 0, 0] := by
  rw [show A10K2.u2840 = KTree.node A10K2.u2838 (nat_lit 46890231) (nat_lit 14693586544) (nat_lit 0) A10K2.u2839 from rfl, totK_node, atot2838, atot2839]
  decide +kernel

theorem arows2846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2846 = true := by
  rw [show A10K2.u2846 = KTree.node A10K2.u2844 (nat_lit 46903227) (nat_lit 6755606656) (nat_lit 0) A10K2.u2845 from rfl, allE_node, arows2844, irow2846, arows2845]
  all_goals rfl

theorem atot2846 : totK PA10K2 A10K2.u2846 = [0, 1338530809648, 5832194684554, 8140973319885, 3982755046536, 551698381969, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2846 = KTree.node A10K2.u2844 (nat_lit 46903227) (nat_lit 6755606656) (nat_lit 0) A10K2.u2845 from rfl, totK_node, atot2844, atot2845]
  decide +kernel

theorem arows2849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2849 = true := by
  rw [show A10K2.u2849 = KTree.node A10K2.u2847 (nat_lit 46922962) (nat_lit 15244508480) (nat_lit 0) A10K2.u2848 from rfl, allE_node, arows2847, irow2849, arows2848]
  all_goals rfl

theorem atot2849 : totK PA10K2 A10K2.u2849 = [0, 1188700740945, 5158442045108, 7666651830991, 4613273467365, 1001372712471, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2849 = KTree.node A10K2.u2847 (nat_lit 46922962) (nat_lit 15244508480) (nat_lit 0) A10K2.u2848 from rfl, totK_node, atot2847, atot2848]
  decide +kernel

theorem arows2853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2853 = true := by
  rw [show A10K2.u2853 = KTree.node A10K2.u2851 (nat_lit 47006963) (nat_lit 10210794581) (nat_lit 0) A10K2.u2852 from rfl, allE_node, arows2851, irow2853, arows2852]
  all_goals rfl

theorem atot2853 : totK PA10K2 A10K2.u2853 = [0, 786156250749, 4368545195645, 8048412541271, 5076546467041, 867515256139, 38008422587, 0, 0, 0] := by
  rw [show A10K2.u2853 = KTree.node A10K2.u2851 (nat_lit 47006963) (nat_lit 10210794581) (nat_lit 0) A10K2.u2852 from rfl, totK_node, atot2851, atot2852]
  decide +kernel

theorem arows2856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2856 = true := by
  rw [show A10K2.u2856 = KTree.node A10K2.u2854 (nat_lit 47019370) (nat_lit 9829067446) (nat_lit 0) A10K2.u2855 from rfl, allE_node, arows2854, irow2856, arows2855]
  all_goals rfl

theorem atot2856 : totK PA10K2 A10K2.u2856 = [0, 656132540036, 3992486883859, 8023572549015, 5908700994105, 1323576171385, 67541609336, 0, 0, 0] := by
  rw [show A10K2.u2856 = KTree.node A10K2.u2854 (nat_lit 47019370) (nat_lit 9829067446) (nat_lit 0) A10K2.u2855 from rfl, totK_node, atot2854, atot2855]
  decide +kernel

theorem arows2861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2861 = true := by
  rw [show A10K2.u2861 = KTree.node A10K2.u2859 (nat_lit 47038721) (nat_lit 8585395254) (nat_lit 0) A10K2.u2860 from rfl, allE_node, arows2859, irow2861, arows2860]
  all_goals rfl

theorem atot2861 : totK PA10K2 A10K2.u2861 = [0, 0, 924329403997, 4891968697934, 8054173592270, 4250039347081, 670973761491, 31018567651, 0, 0] := by
  rw [show A10K2.u2861 = KTree.node A10K2.u2859 (nat_lit 47038721) (nat_lit 8585395254) (nat_lit 0) A10K2.u2860 from rfl, totK_node, atot2859, atot2860]
  decide +kernel

theorem arows2864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2864 = true := by
  rw [show A10K2.u2864 = KTree.node A10K2.u2862 (nat_lit 47064876) (nat_lit 13098636310) (nat_lit 0) A10K2.u2863 from rfl, allE_node, arows2862, irow2864, arows2863]
  all_goals rfl

theorem atot2864 : totK PA10K2 A10K2.u2864 = [0, 796027745624, 4281260928433, 7671713173317, 5343697730078, 1539831408199, 193157828359, 5685526223, 0, 0] := by
  rw [show A10K2.u2864 = KTree.node A10K2.u2862 (nat_lit 47064876) (nat_lit 13098636310) (nat_lit 0) A10K2.u2863 from rfl, totK_node, atot2862, atot2863]
  decide +kernel

theorem arows2868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2868 = true := by
  rw [show A10K2.u2868 = KTree.node A10K2.u2866 (nat_lit 47075436) (nat_lit 11510078813) (nat_lit 0) A10K2.u2867 from rfl, allE_node, arows2866, irow2868, arows2867]
  all_goals rfl

theorem atot2868 : totK PA10K2 A10K2.u2868 = [0, 742077765612, 4223566053427, 7905213877543, 5266150066904, 976766417977, 38505033050, 0, 0, 0] := by
  rw [show A10K2.u2868 = KTree.node A10K2.u2866 (nat_lit 47075436) (nat_lit 11510078813) (nat_lit 0) A10K2.u2867 from rfl, totK_node, atot2866, atot2867]
  decide +kernel

theorem arows2871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2871 = true := by
  rw [show A10K2.u2871 = KTree.node A10K2.u2869 (nat_lit 47108378) (nat_lit 11511869346) (nat_lit 0) A10K2.u2870 from rfl, allE_node, arows2869, irow2871, arows2870]
  all_goals rfl

theorem atot2871 : totK PA10K2 A10K2.u2871 = [0, 556621861187, 3004131383059, 6534991755832, 6547680800980, 2318199601465, 258715959954, 6239673734, 0, 0] := by
  rw [show A10K2.u2871 = KTree.node A10K2.u2869 (nat_lit 47108378) (nat_lit 11511869346) (nat_lit 0) A10K2.u2870 from rfl, totK_node, atot2869, atot2870]
  decide +kernel

theorem arows2878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2878 = true := by
  rw [show A10K2.u2878 = KTree.node A10K2.u2876 (nat_lit 47132059) (nat_lit 9623650143) (nat_lit 0) A10K2.u2877 from rfl, allE_node, arows2876, irow2878, arows2877]
  all_goals rfl

theorem atot2878 : totK PA10K2 A10K2.u2878 = [0, 1050582063700, 4979457171905, 8021295058787, 4856666137353, 912581299257, 38293342501, 0, 0, 0] := by
  rw [show A10K2.u2878 = KTree.node A10K2.u2876 (nat_lit 47132059) (nat_lit 9623650143) (nat_lit 0) A10K2.u2877 from rfl, totK_node, atot2876, atot2877]
  decide +kernel

theorem arows2881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2881 = true := by
  rw [show A10K2.u2881 = KTree.node A10K2.u2879 (nat_lit 47150250) (nat_lit 12779633272) (nat_lit 0) A10K2.u2880 from rfl, allE_node, arows2879, irow2881, arows2880]
  all_goals rfl

theorem atot2881 : totK PA10K2 A10K2.u2881 = [480657707117, 2190438541788, 4820851019412, 6638518019976, 4507456379756, 1060485468011, 62382159641, 0, 0, 0] := by
  rw [show A10K2.u2881 = KTree.node A10K2.u2879 (nat_lit 47150250) (nat_lit 12779633272) (nat_lit 0) A10K2.u2880 from rfl, totK_node, atot2879, atot2880]
  decide +kernel

theorem arows2885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2885 = true := by
  rw [show A10K2.u2885 = KTree.node A10K2.u2883 (nat_lit 47717854) (nat_lit 14811449216) (nat_lit 0) A10K2.u2884 from rfl, allE_node, arows2883, irow2885, arows2884]
  all_goals rfl

theorem atot2885 : totK PA10K2 A10K2.u2885 = [1212626062150, 5468806186754, 8162292175964, 4251039145848, 687570356072, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2885 = KTree.node A10K2.u2883 (nat_lit 47717854) (nat_lit 14811449216) (nat_lit 0) A10K2.u2884 from rfl, totK_node, atot2883, atot2884]
  decide +kernel

theorem arows2888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2888 = true := by
  rw [show A10K2.u2888 = KTree.node A10K2.u2886 (nat_lit 47742675) (nat_lit 9367519865) (nat_lit 0) A10K2.u2887 from rfl, allE_node, arows2886, irow2888, arows2887]
  all_goals rfl

theorem atot2888 : totK PA10K2 A10K2.u2888 = [177435414779, 2438409014953, 7398386956707, 7567579032179, 2264250176824, 149191310666, 0, 0, 0, 0] := by
  rw [show A10K2.u2888 = KTree.node A10K2.u2886 (nat_lit 47742675) (nat_lit 9367519865) (nat_lit 0) A10K2.u2887 from rfl, totK_node, atot2886, atot2887]
  decide +kernel

theorem arows2893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2893 = true := by
  rw [show A10K2.u2893 = KTree.node A10K2.u2891 (nat_lit 47767990) (nat_lit 16849478543) (nat_lit 0) A10K2.u2892 from rfl, allE_node, arows2891, irow2893, arows2892]
  all_goals rfl

theorem atot2893 : totK PA10K2 A10K2.u2893 = [312139800791, 2190997624655, 5870786385356, 7160936934726, 3490527403371, 605418990860, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2893 = KTree.node A10K2.u2891 (nat_lit 47767990) (nat_lit 16849478543) (nat_lit 0) A10K2.u2892 from rfl, totK_node, atot2891, atot2892]
  decide +kernel

theorem arows2896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2896 = true := by
  rw [show A10K2.u2896 = KTree.node A10K2.u2894 (nat_lit 47790764) (nat_lit 12558426789) (nat_lit 0) A10K2.u2895 from rfl, allE_node, arows2894, irow2896, arows2895]
  all_goals rfl

theorem atot2896 : totK PA10K2 A10K2.u2896 = [991932798489, 4972369781821, 8143181126513, 4667323206939, 776376731776, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2896 = KTree.node A10K2.u2894 (nat_lit 47790764) (nat_lit 12558426789) (nat_lit 0) A10K2.u2895 from rfl, totK_node, atot2894, atot2895]
  decide +kernel

theorem arows2900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2900 = true := by
  rw [show A10K2.u2900 = KTree.node A10K2.u2898 (nat_lit 47804935) (nat_lit 13480386925) (nat_lit 0) A10K2.u2899 from rfl, allE_node, arows2898, irow2900, arows2899]
  all_goals rfl

theorem atot2900 : totK PA10K2 A10K2.u2900 = [829662196464, 4193322581227, 7652881339059, 5837844909540, 1539390727483, 95812067308, 0, 0, 0, 0] := by
  rw [show A10K2.u2900 = KTree.node A10K2.u2898 (nat_lit 47804935) (nat_lit 13480386925) (nat_lit 0) A10K2.u2899 from rfl, totK_node, atot2898, atot2899]
  decide +kernel

theorem arows2903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2903 = true := by
  rw [show A10K2.u2903 = KTree.node A10K2.u2901 (nat_lit 47823643) (nat_lit 8687435763) (nat_lit 0) A10K2.u2902 from rfl, allE_node, arows2901, irow2903, arows2902]
  all_goals rfl

theorem atot2903 : totK PA10K2 A10K2.u2903 = [0, 1075218698214, 5019286069157, 7906755429803, 4439518324110, 792953588447, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2903 = KTree.node A10K2.u2901 (nat_lit 47823643) (nat_lit 8687435763) (nat_lit 0) A10K2.u2902 from rfl, totK_node, atot2901, atot2902]
  decide +kernel

theorem arows2909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2909 = true := by
  rw [show A10K2.u2909 = KTree.node A10K2.u2907 (nat_lit 47907363) (nat_lit 3200590304) (nat_lit 0) A10K2.u2908 from rfl, allE_node, arows2907, irow2909, arows2908]
  all_goals rfl

theorem atot2909 : totK PA10K2 A10K2.u2909 = [725949308331, 3831948864416, 7405945573812, 5853742157968, 1603273806720, 107664955447, 0, 0, 0, 0] := by
  rw [show A10K2.u2909 = KTree.node A10K2.u2907 (nat_lit 47907363) (nat_lit 3200590304) (nat_lit 0) A10K2.u2908 from rfl, totK_node, atot2907, atot2908]
  decide +kernel

theorem arows2912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2912 = true := by
  rw [show A10K2.u2912 = KTree.node A10K2.u2910 (nat_lit 47920353) (nat_lit 2977021011) (nat_lit 0) A10K2.u2911 from rfl, allE_node, arows2910, irow2912, arows2911]
  all_goals rfl

theorem atot2912 : totK PA10K2 A10K2.u2912 = [1330847583291, 5599970012182, 7975614202083, 4187073206915, 693396657769, 31450896759, 0, 0, 0, 0] := by
  rw [show A10K2.u2912 = KTree.node A10K2.u2910 (nat_lit 47920353) (nat_lit 2977021011) (nat_lit 0) A10K2.u2911 from rfl, totK_node, atot2910, atot2911]
  decide +kernel

theorem arows2916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2916 = true := by
  rw [show A10K2.u2916 = KTree.node A10K2.u2914 (nat_lit 47937435) (nat_lit 8693236484) (nat_lit 0) A10K2.u2915 from rfl, allE_node, arows2914, irow2916, arows2915]
  all_goals rfl

theorem atot2916 : totK PA10K2 A10K2.u2916 = [332208314330, 3148408083203, 7887749202286, 6704659295297, 1648864664607, 87724154910, 0, 0, 0, 0] := by
  rw [show A10K2.u2916 = KTree.node A10K2.u2914 (nat_lit 47937435) (nat_lit 8693236484) (nat_lit 0) A10K2.u2915 from rfl, totK_node, atot2914, atot2915]
  decide +kernel

theorem arows2919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2919 = true := by
  rw [show A10K2.u2919 = KTree.node A10K2.u2917 (nat_lit 47950101) (nat_lit 6347210428) (nat_lit 0) A10K2.u2918 from rfl, allE_node, arows2917, irow2919, arows2918]
  all_goals rfl

theorem atot2919 : totK PA10K2 A10K2.u2919 = [0, 932389315957, 4868865362089, 8299848483809, 4759165304584, 693072477966, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2919 = KTree.node A10K2.u2917 (nat_lit 47950101) (nat_lit 6347210428) (nat_lit 0) A10K2.u2918 from rfl, totK_node, atot2917, atot2918]
  decide +kernel

theorem arows2924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2924 = true := by
  rw [show A10K2.u2924 = KTree.node A10K2.u2922 (nat_lit 47968808) (nat_lit 12309901778) (nat_lit 0) A10K2.u2923 from rfl, allE_node, arows2922, irow2924, arows2923]
  all_goals rfl

theorem atot2924 : totK PA10K2 A10K2.u2924 = [0, 1074292103986, 4955759034261, 7800442064822, 4815409571037, 1018470278411, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2924 = KTree.node A10K2.u2922 (nat_lit 47968808) (nat_lit 12309901778) (nat_lit 0) A10K2.u2923 from rfl, totK_node, atot2922, atot2923]
  decide +kernel

theorem arows2927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2927 = true := by
  rw [show A10K2.u2927 = KTree.node A10K2.u2925 (nat_lit 47979678) (nat_lit 15128163591) (nat_lit 0) A10K2.u2926 from rfl, allE_node, arows2925, irow2927, arows2926]
  all_goals rfl

theorem atot2927 : totK PA10K2 A10K2.u2927 = [0, 1187922603457, 5507854359098, 8149984619453, 4167453024738, 677084495503, 30780440178, 0, 0, 0] := by
  rw [show A10K2.u2927 = KTree.node A10K2.u2925 (nat_lit 47979678) (nat_lit 15128163591) (nat_lit 0) A10K2.u2926 from rfl, totK_node, atot2925, atot2926]
  decide +kernel

theorem arows2931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2931 = true := by
  rw [show A10K2.u2931 = KTree.node A10K2.u2929 (nat_lit 48004617) (nat_lit 8532830397) (nat_lit 0) A10K2.u2930 from rfl, allE_node, arows2929, irow2931, arows2930]
  all_goals rfl

theorem atot2931 : totK PA10K2 A10K2.u2931 = [0, 320910162593, 2780944440112, 7462790348067, 7250297864930, 2117252606213, 142915131340, 0, 0, 0] := by
  rw [show A10K2.u2931 = KTree.node A10K2.u2929 (nat_lit 48004617) (nat_lit 8532830397) (nat_lit 0) A10K2.u2930 from rfl, totK_node, atot2929, atot2930]
  decide +kernel

theorem arows2934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2934 = true := by
  rw [show A10K2.u2934 = KTree.node A10K2.u2932 (nat_lit 48031113) (nat_lit 8181611024) (nat_lit 0) A10K2.u2933 from rfl, allE_node, arows2932, irow2934, arows2933]
  all_goals rfl

theorem atot2934 : totK PA10K2 A10K2.u2934 = [0, 525241347744, 3006563453233, 6565024631704, 6558827252660, 2578112492278, 321937034971, 7007974415, 0, 0] := by
  rw [show A10K2.u2934 = KTree.node A10K2.u2932 (nat_lit 48031113) (nat_lit 8181611024) (nat_lit 0) A10K2.u2933 from rfl, totK_node, atot2932, atot2933]
  decide +kernel

theorem arows2942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2942 = true := by
  rw [show A10K2.u2942 = KTree.node A10K2.u2940 (nat_lit 48055442) (nat_lit 15795371065) (nat_lit 0) A10K2.u2941 from rfl, allE_node, arows2940, irow2942, arows2941]
  all_goals rfl

theorem atot2942 : totK PA10K2 A10K2.u2942 = [0, 992732881053, 4909123342251, 8090833494285, 4815231341950, 857925341633, 37546598172, 0, 0, 0] := by
  rw [show A10K2.u2942 = KTree.node A10K2.u2940 (nat_lit 48055442) (nat_lit 15795371065) (nat_lit 0) A10K2.u2941 from rfl, totK_node, atot2940, atot2941]
  decide +kernel

theorem arows2945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2945 = true := by
  rw [show A10K2.u2945 = KTree.node A10K2.u2943 (nat_lit 48068080) (nat_lit 12543459035) (nat_lit 0) A10K2.u2944 from rfl, allE_node, arows2943, irow2945, arows2944]
  all_goals rfl

theorem atot2945 : totK PA10K2 A10K2.u2945 = [0, 613762948205, 3708660758125, 7736144013829, 6252700674267, 1588751056032, 94106083090, 0, 0, 0] := by
  rw [show A10K2.u2945 = KTree.node A10K2.u2943 (nat_lit 48068080) (nat_lit 12543459035) (nat_lit 0) A10K2.u2944 from rfl, totK_node, atot2943, atot2944]
  decide +kernel

theorem arows2949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2949 = true := by
  rw [show A10K2.u2949 = KTree.node A10K2.u2947 (nat_lit 48089331) (nat_lit 9941396732) (nat_lit 0) A10K2.u2948 from rfl, allE_node, arows2947, irow2949, arows2948]
  all_goals rfl

theorem atot2949 : totK PA10K2 A10K2.u2949 = [0, 113839911969, 1762696424410, 6312388122348, 7984512429011, 3329931465410, 379116771022, 7151180950, 0, 0] := by
  rw [show A10K2.u2949 = KTree.node A10K2.u2947 (nat_lit 48089331) (nat_lit 9941396732) (nat_lit 0) A10K2.u2948 from rfl, totK_node, atot2947, atot2948]
  decide +kernel

theorem arows2952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2952 = true := by
  rw [show A10K2.u2952 = KTree.node A10K2.u2950 (nat_lit 48175109) (nat_lit 6492888296) (nat_lit 0) A10K2.u2951 from rfl, allE_node, arows2950, irow2952, arows2951]
  all_goals rfl

theorem atot2952 : totK PA10K2 A10K2.u2952 = [0, 1380838132820, 5907563462017, 7956032780206, 3694176411970, 514107968230, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u2952 = KTree.node A10K2.u2950 (nat_lit 48175109) (nat_lit 6492888296) (nat_lit 0) A10K2.u2951 from rfl, totK_node, atot2950, atot2951]
  decide +kernel

theorem arows2957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2957 = true := by
  rw [show A10K2.u2957 = KTree.node A10K2.u2955 (nat_lit 48194842) (nat_lit 14643091517) (nat_lit 0) A10K2.u2956 from rfl, allE_node, arows2955, irow2957, arows2956]
  all_goals rfl

theorem atot2957 : totK PA10K2 A10K2.u2957 = [0, 891342416461, 4660221501426, 8235698900763, 5212242373629, 836995510690, 18992036149, 0, 0, 0] := by
  rw [show A10K2.u2957 = KTree.node A10K2.u2955 (nat_lit 48194842) (nat_lit 14643091517) (nat_lit 0) A10K2.u2956 from rfl, totK_node, atot2955, atot2956]
  decide +kernel

theorem arows2960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2960 = true := by
  rw [show A10K2.u2960 = KTree.node A10K2.u2958 (nat_lit 48205312) (nat_lit 15548134428) (nat_lit 0) A10K2.u2959 from rfl, allE_node, arows2958, irow2960, arows2959]
  all_goals rfl

theorem atot2960 : totK PA10K2 A10K2.u2960 = [0, 0, 1497529732665, 6121616359660, 8141978778218, 3433427838226, 352929604409, 6318667960, 0, 0] := by
  rw [show A10K2.u2960 = KTree.node A10K2.u2958 (nat_lit 48205312) (nat_lit 15548134428) (nat_lit 0) A10K2.u2959 from rfl, totK_node, atot2958, atot2959]
  decide +kernel

theorem arows2964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2964 = true := by
  rw [show A10K2.u2964 = KTree.node A10K2.u2962 (nat_lit 48226825) (nat_lit 9612534347) (nat_lit 0) A10K2.u2963 from rfl, allE_node, arows2962, irow2964, arows2963]
  all_goals rfl

theorem atot2964 : totK PA10K2 A10K2.u2964 = [0, 0, 1203865259521, 5642115226037, 8224480075335, 4130633896305, 540179533320, 12460675034, 0, 0] := by
  rw [show A10K2.u2964 = KTree.node A10K2.u2962 (nat_lit 48226825) (nat_lit 9612534347) (nat_lit 0) A10K2.u2963 from rfl, totK_node, atot2962, atot2963]
  decide +kernel

theorem arows2967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2967 = true := by
  rw [show A10K2.u2967 = KTree.node A10K2.u2965 (nat_lit 48236845) (nat_lit 6639878160) (nat_lit 0) A10K2.u2966 from rfl, allE_node, arows2965, irow2967, arows2966]
  all_goals rfl

theorem atot2967 : totK PA10K2 A10K2.u2967 = [0, 844719840339, 3747508790327, 6058491233280, 5072053833576, 2816294722912, 751102515933, 54997142734, 0, 0] := by
  rw [show A10K2.u2967 = KTree.node A10K2.u2965 (nat_lit 48236845) (nat_lit 6639878160) (nat_lit 0) A10K2.u2966 from rfl, totK_node, atot2965, atot2966]
  decide +kernel

theorem arows2973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2973 = true := by
  rw [show A10K2.u2973 = KTree.node A10K2.u2971 (nat_lit 48257572) (nat_lit 13617786596) (nat_lit 0) A10K2.u2972 from rfl, allE_node, arows2971, irow2973, arows2972]
  all_goals rfl

theorem atot2973 : totK PA10K2 A10K2.u2973 = [0, 1361137082739, 5925854105443, 8258849360922, 3676558618555, 394607135446, 5976421810, 0, 0, 0] := by
  rw [show A10K2.u2973 = KTree.node A10K2.u2971 (nat_lit 48257572) (nat_lit 13617786596) (nat_lit 0) A10K2.u2972 from rfl, totK_node, atot2971, atot2972]
  decide +kernel

theorem arows2976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2976 = true := by
  rw [show A10K2.u2976 = KTree.node A10K2.u2974 (nat_lit 48269318) (nat_lit 13258206685) (nat_lit 0) A10K2.u2975 from rfl, allE_node, arows2974, irow2976, arows2975]
  all_goals rfl

theorem atot2976 : totK PA10K2 A10K2.u2976 = [0, 0, 1417859343778, 6035409638613, 8003789953013, 3500937984564, 518448101430, 25239774317, 0, 0] := by
  rw [show A10K2.u2976 = KTree.node A10K2.u2974 (nat_lit 48269318) (nat_lit 13258206685) (nat_lit 0) A10K2.u2975 from rfl, totK_node, atot2974, atot2975]
  decide +kernel

theorem arows2980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2980 = true := by
  rw [show A10K2.u2980 = KTree.node A10K2.u2978 (nat_lit 48290092) (nat_lit 13552313479) (nat_lit 0) A10K2.u2979 from rfl, allE_node, arows2978, irow2980, arows2979]
  all_goals rfl

theorem atot2980 : totK PA10K2 A10K2.u2980 = [0, 193918436879, 1773584425395, 5999573891473, 7727301333621, 3278132563390, 419420303232, 10957026886, 0, 0] := by
  rw [show A10K2.u2980 = KTree.node A10K2.u2978 (nat_lit 48290092) (nat_lit 13552313479) (nat_lit 0) A10K2.u2979 from rfl, totK_node, atot2978, atot2979]
  decide +kernel

theorem arows2983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2983 = true := by
  rw [show A10K2.u2983 = KTree.node A10K2.u2981 (nat_lit 48436110) (nat_lit 13488965938) (nat_lit 0) A10K2.u2982 from rfl, allE_node, arows2981, irow2983, arows2982]
  all_goals rfl

theorem atot2983 : totK PA10K2 A10K2.u2983 = [0, 1184593587114, 5528626054151, 8222276984204, 4252384706140, 687435188074, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u2983 = KTree.node A10K2.u2981 (nat_lit 48436110) (nat_lit 13488965938) (nat_lit 0) A10K2.u2982 from rfl, totK_node, atot2981, atot2982]
  decide +kernel

theorem arows2988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2988 = true := by
  rw [show A10K2.u2988 = KTree.node A10K2.u2986 (nat_lit 48458924) (nat_lit 4434378434) (nat_lit 0) A10K2.u2987 from rfl, allE_node, arows2986, irow2988, arows2987]
  all_goals rfl

theorem atot2988 : totK PA10K2 A10K2.u2988 = [0, 866737529530, 4530309974488, 8149311617070, 5441939993341, 1038777413647, 32390479138, 0, 0, 0] := by
  rw [show A10K2.u2988 = KTree.node A10K2.u2986 (nat_lit 48458924) (nat_lit 4434378434) (nat_lit 0) A10K2.u2987 from rfl, totK_node, atot2986, atot2987]
  decide +kernel

theorem arows2991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2991 = true := by
  rw [show A10K2.u2991 = KTree.node A10K2.u2989 (nat_lit 48468230) (nat_lit 11657215689) (nat_lit 0) A10K2.u2990 from rfl, allE_node, arows2989, irow2991, arows2990]
  all_goals rfl

theorem atot2991 : totK PA10K2 A10K2.u2991 = [0, 0, 1377329814583, 5941108510415, 8284897227980, 3795692327459, 435972770383, 6904928264, 0, 0] := by
  rw [show A10K2.u2991 = KTree.node A10K2.u2989 (nat_lit 48468230) (nat_lit 11657215689) (nat_lit 0) A10K2.u2990 from rfl, totK_node, atot2989, atot2990]
  decide +kernel

theorem arows2995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2995 = true := by
  rw [show A10K2.u2995 = KTree.node A10K2.u2993 (nat_lit 48490427) (nat_lit 7007213943) (nat_lit 0) A10K2.u2994 from rfl, allE_node, arows2993, irow2995, arows2994]
  all_goals rfl

theorem atot2995 : totK PA10K2 A10K2.u2995 = [0, 0, 865937196027, 4722924639705, 8329779204523, 5143816967768, 763329380355, 18990462437, 0, 0] := by
  rw [show A10K2.u2995 = KTree.node A10K2.u2993 (nat_lit 48490427) (nat_lit 7007213943) (nat_lit 0) A10K2.u2994 from rfl, totK_node, atot2993, atot2994]
  decide +kernel

theorem arows2998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2998 = true := by
  rw [show A10K2.u2998 = KTree.node A10K2.u2996 (nat_lit 48500634) (nat_lit 11680800211) (nat_lit 0) A10K2.u2997 from rfl, allE_node, arows2996, irow2998, arows2997]
  all_goals rfl

theorem atot2998 : totK PA10K2 A10K2.u2998 = [0, 0, 1136639156795, 4898464624666, 7411515055761, 4630269636042, 1129747412363, 79717692957, 0, 0] := by
  rw [show A10K2.u2998 = KTree.node A10K2.u2996 (nat_lit 48500634) (nat_lit 11680800211) (nat_lit 0) A10K2.u2997 from rfl, totK_node, atot2996, atot2997]
  decide +kernel

theorem arows3005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3005 = true := by
  rw [show A10K2.u3005 = KTree.node A10K2.u3003 (nat_lit 48522426) (nat_lit 14794508169) (nat_lit 0) A10K2.u3004 from rfl, allE_node, arows3003, irow3005, arows3004]
  all_goals rfl

theorem atot3005 : totK PA10K2 A10K2.u3005 = [0, 0, 1069217766283, 5324992983672, 8338178355431, 4314949228243, 579346738690, 12558367923, 0, 0] := by
  rw [show A10K2.u3005 = KTree.node A10K2.u3003 (nat_lit 48522426) (nat_lit 14794508169) (nat_lit 0) A10K2.u3004 from rfl, totK_node, atot3003, atot3004]
  decide +kernel

theorem arows3008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3008 = true := by
  rw [show A10K2.u3008 = KTree.node A10K2.u3006 (nat_lit 48533511) (nat_lit 13439709835) (nat_lit 0) A10K2.u3007 from rfl, allE_node, arows3006, irow3008, arows3007]
  all_goals rfl

theorem atot3008 : totK PA10K2 A10K2.u3008 = [0, 0, 0, 1403653520004, 6199171352315, 7940711196805, 3115823826852, 374912058166, 7237400819, 0] := by
  rw [show A10K2.u3008 = KTree.node A10K2.u3006 (nat_lit 48533511) (nat_lit 13439709835) (nat_lit 0) A10K2.u3007 from rfl, totK_node, atot3006, atot3007]
  decide +kernel

theorem arows3012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3012 = true := by
  rw [show A10K2.u3012 = KTree.node A10K2.u3010 (nat_lit 48694206) (nat_lit 16010971158) (nat_lit 0) A10K2.u3011 from rfl, allE_node, arows3010, irow3012, arows3011]
  all_goals rfl

theorem atot3012 : totK PA10K2 A10K2.u3012 = [0, 0, 783941292525, 4393544131775, 7979547687627, 5405008487507, 1146448512561, 59776692374, 0, 0] := by
  rw [show A10K2.u3012 = KTree.node A10K2.u3010 (nat_lit 48694206) (nat_lit 16010971158) (nat_lit 0) A10K2.u3011 from rfl, totK_node, atot3010, atot3011]
  decide +kernel

theorem arows3015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3015 = true := by
  rw [show A10K2.u3015 = KTree.node A10K2.u3013 (nat_lit 48709015) (nat_lit 14535722111) (nat_lit 0) A10K2.u3014 from rfl, allE_node, arows3013, irow3015, arows3014]
  all_goals rfl

theorem atot3015 : totK PA10K2 A10K2.u3015 = [0, 0, 1461030758416, 6107856172052, 8244636194096, 3822514241639, 430391781771, 6860445330, 0, 0] := by
  rw [show A10K2.u3015 = KTree.node A10K2.u3013 (nat_lit 48709015) (nat_lit 14535722111) (nat_lit 0) A10K2.u3014 from rfl, totK_node, atot3013, atot3014]
  decide +kernel

theorem arows3020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3020 = true := by
  rw [show A10K2.u3020 = KTree.node A10K2.u3018 (nat_lit 48834273) (nat_lit 3829419801) (nat_lit 0) A10K2.u3019 from rfl, allE_node, arows3018, irow3020, arows3019]
  all_goals rfl

theorem atot3020 : totK PA10K2 A10K2.u3020 = [0, 861896674927, 3560020128145, 5498882452401, 5218921975531, 3585532419960, 962002626865, 62368562949, 0, 0] := by
  rw [show A10K2.u3020 = KTree.node A10K2.u3018 (nat_lit 48834273) (nat_lit 3829419801) (nat_lit 0) A10K2.u3019 from rfl, totK_node, atot3018, atot3019]
  decide +kernel

theorem arows3023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3023 = true := by
  rw [show A10K2.u3023 = KTree.node A10K2.u3021 (nat_lit 48843606) (nat_lit 8161741798) (nat_lit 0) A10K2.u3022 from rfl, allE_node, arows3021, irow3023, arows3022]
  all_goals rfl

theorem atot3023 : totK PA10K2 A10K2.u3023 = [0, 1307523594038, 5588942672377, 8026667096485, 3942022960690, 506244818855, 12016267967, 0, 0, 0] := by
  rw [show A10K2.u3023 = KTree.node A10K2.u3021 (nat_lit 48843606) (nat_lit 8161741798) (nat_lit 0) A10K2.u3022 from rfl, totK_node, atot3021, atot3022]
  decide +kernel

theorem arows3027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3027 = true := by
  rw [show A10K2.u3027 = KTree.node A10K2.u3025 (nat_lit 48856987) (nat_lit 7927819500) (nat_lit 0) A10K2.u3026 from rfl, allE_node, arows3025, irow3027, arows3026]
  all_goals rfl

theorem atot3027 : totK PA10K2 A10K2.u3027 = [0, 119627100822, 2456546494400, 7467352094529, 7453667102258, 2245920669884, 150991016996, 0, 0, 0] := by
  rw [show A10K2.u3027 = KTree.node A10K2.u3025 (nat_lit 48856987) (nat_lit 7927819500) (nat_lit 0) A10K2.u3026 from rfl, totK_node, atot3025, atot3026]
  decide +kernel

theorem arows3030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3030 = true := by
  rw [show A10K2.u3030 = KTree.node A10K2.u3028 (nat_lit 48875560) (nat_lit 11261750635) (nat_lit 0) A10K2.u3029 from rfl, allE_node, arows3028, irow3030, arows3029]
  all_goals rfl

theorem atot3030 : totK PA10K2 A10K2.u3030 = [0, 0, 1127714576685, 5089613747284, 7777565864856, 4237444712193, 753726230502, 36968589557, 0, 0] := by
  rw [show A10K2.u3030 = KTree.node A10K2.u3028 (nat_lit 48875560) (nat_lit 11261750635) (nat_lit 0) A10K2.u3029 from rfl, totK_node, atot3028, atot3029]
  decide +kernel

theorem arows3036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3036 = true := by
  rw [show A10K2.u3036 = KTree.node A10K2.u3034 (nat_lit 48900798) (nat_lit 12985493537) (nat_lit 0) A10K2.u3035 from rfl, allE_node, arows3034, irow3036, arows3035]
  all_goals rfl

theorem atot3036 : totK PA10K2 A10K2.u3036 = [0, 899071735456, 4231080165237, 7474646167855, 5626771820809, 1518776082806, 107895539461, 0, 0, 0] := by
  rw [show A10K2.u3036 = KTree.node A10K2.u3034 (nat_lit 48900798) (nat_lit 12985493537) (nat_lit 0) A10K2.u3035 from rfl, totK_node, atot3034, atot3035]
  decide +kernel

theorem arows3039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3039 = true := by
  rw [show A10K2.u3039 = KTree.node A10K2.u3037 (nat_lit 48912497) (nat_lit 5651202163) (nat_lit 0) A10K2.u3038 from rfl, allE_node, arows3037, irow3039, arows3038]
  all_goals rfl

theorem atot3039 : totK PA10K2 A10K2.u3039 = [0, 639500710750, 4088335415707, 7973213573421, 5465443410456, 1097270920582, 45698759736, 0, 0, 0] := by
  rw [show A10K2.u3039 = KTree.node A10K2.u3037 (nat_lit 48912497) (nat_lit 5651202163) (nat_lit 0) A10K2.u3038 from rfl, totK_node, atot3037, atot3038]
  decide +kernel

theorem arows3043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3043 = true := by
  rw [show A10K2.u3043 = KTree.node A10K2.u3041 (nat_lit 48945370) (nat_lit 11789690737) (nat_lit 0) A10K2.u3042 from rfl, allE_node, arows3041, irow3043, arows3042]
  all_goals rfl

theorem atot3043 : totK PA10K2 A10K2.u3043 = [0, 556621861187, 2964130636219, 6526194491859, 6478109730784, 2297322400519, 258013140434, 6354482628, 0, 0] := by
  rw [show A10K2.u3043 = KTree.node A10K2.u3041 (nat_lit 48945370) (nat_lit 11789690737) (nat_lit 0) A10K2.u3042 from rfl, totK_node, atot3041, atot3042]
  decide +kernel

theorem arows3046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3046 = true := by
  rw [show A10K2.u3046 = KTree.node A10K2.u3044 (nat_lit 48968865) (nat_lit 4577633285) (nat_lit 0) A10K2.u3045 from rfl, allE_node, arows3044, irow3046, arows3045]
  all_goals rfl

theorem atot3046 : totK PA10K2 A10K2.u3046 = [0, 1294291640740, 5545738951905, 7949723148975, 4268412592803, 737459820884, 31522233512, 0, 0, 0] := by
  rw [show A10K2.u3046 = KTree.node A10K2.u3044 (nat_lit 48968865) (nat_lit 4577633285) (nat_lit 0) A10K2.u3045 from rfl, totK_node, atot3044, atot3045]
  decide +kernel

theorem arows3051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3051 = true := by
  rw [show A10K2.u3051 = KTree.node A10K2.u3049 (nat_lit 48985998) (nat_lit 14724698798) (nat_lit 0) A10K2.u3050 from rfl, allE_node, arows3049, irow3051, arows3050]
  all_goals rfl

theorem atot3051 : totK PA10K2 A10K2.u3051 = [0, 359360087617, 3095161198117, 7604336677031, 6821896871266, 1998604797438, 135119369337, 0, 0, 0] := by
  rw [show A10K2.u3051 = KTree.node A10K2.u3049 (nat_lit 48985998) (nat_lit 14724698798) (nat_lit 0) A10K2.u3050 from rfl, totK_node, atot3049, atot3050]
  decide +kernel

theorem arows3054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3054 = true := by
  rw [show A10K2.u3054 = KTree.node A10K2.u3052 (nat_lit 48999931) (nat_lit 6239094582) (nat_lit 0) A10K2.u3053 from rfl, allE_node, arows3052, irow3054, arows3053]
  all_goals rfl

theorem atot3054 : totK PA10K2 A10K2.u3054 = [0, 0, 1199816808971, 5434501670517, 8157281674697, 4330093808579, 593459853509, 13679205470, 0, 0] := by
  rw [show A10K2.u3054 = KTree.node A10K2.u3052 (nat_lit 48999931) (nat_lit 6239094582) (nat_lit 0) A10K2.u3053 from rfl, totK_node, atot3052, atot3053]
  decide +kernel

theorem arows3058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3058 = true := by
  rw [show A10K2.u3058 = KTree.node A10K2.u3056 (nat_lit 49018614) (nat_lit 15310652498) (nat_lit 0) A10K2.u3057 from rfl, allE_node, arows3056, irow3058, arows3057]
  all_goals rfl

theorem atot3058 : totK PA10K2 A10K2.u3058 = [0, 0, 1168444784131, 5116275656232, 7637713320713, 4652729553935, 1011847991688, 61110126106, 0, 0] := by
  rw [show A10K2.u3058 = KTree.node A10K2.u3056 (nat_lit 49018614) (nat_lit 15310652498) (nat_lit 0) A10K2.u3057 from rfl, totK_node, atot3056, atot3057]
  decide +kernel

theorem arows3061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3061 = true := by
  rw [show A10K2.u3061 = KTree.node A10K2.u3059 (nat_lit 49103200) (nat_lit 11271538069) (nat_lit 0) A10K2.u3060 from rfl, allE_node, arows3059, irow3061, arows3060]
  all_goals rfl

theorem atot3061 : totK PA10K2 A10K2.u3061 = [0, 0, 805295234454, 4537131650030, 8064974719138, 4889902258028, 834816232952, 37525842271, 0, 0] := by
  rw [show A10K2.u3061 = KTree.node A10K2.u3059 (nat_lit 49103200) (nat_lit 11271538069) (nat_lit 0) A10K2.u3060 from rfl, totK_node, atot3059, atot3060]
  decide +kernel

theorem arows3072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3072 = true := by
  rw [show A10K2.u3072 = KTree.node A10K2.u3070 (nat_lit 49116382) (nat_lit 11389925001) (nat_lit 0) A10K2.u3071 from rfl, allE_node, arows3070, irow3072, arows3071]
  all_goals rfl

theorem atot3072 : totK PA10K2 A10K2.u3072 = [0, 0, 776975258324, 4272685090090, 7954251813917, 5618011118013, 1269144112576, 67324059887, 0, 0] := by
  rw [show A10K2.u3072 = KTree.node A10K2.u3070 (nat_lit 49116382) (nat_lit 11389925001) (nat_lit 0) A10K2.u3071 from rfl, totK_node, atot3070, atot3071]
  decide +kernel

theorem arows3075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3075 = true := by
  rw [show A10K2.u3075 = KTree.node A10K2.u3073 (nat_lit 49136880) (nat_lit 5215481718) (nat_lit 0) A10K2.u3074 from rfl, allE_node, arows3073, irow3075, arows3074]
  all_goals rfl

theorem atot3075 : totK PA10K2 A10K2.u3075 = [0, 0, 0, 1715790060579, 6739261848202, 7789596507890, 2845144703924, 334693466903, 7380853412, 0] := by
  rw [show A10K2.u3075 = KTree.node A10K2.u3073 (nat_lit 49136880) (nat_lit 5215481718) (nat_lit 0) A10K2.u3074 from rfl, totK_node, atot3073, atot3074]
  decide +kernel

theorem arows3079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3079 = true := by
  rw [show A10K2.u3079 = KTree.node A10K2.u3077 (nat_lit 49168964) (nat_lit 11135578240) (nat_lit 0) A10K2.u3078 from rfl, allE_node, arows3077, irow3079, arows3078]
  all_goals rfl

theorem atot3079 : totK PA10K2 A10K2.u3079 = [0, 0, 1538105511236, 6333009656491, 7911797268949, 3058677831374, 460104643791, 31276155898, 0, 0] := by
  rw [show A10K2.u3079 = KTree.node A10K2.u3077 (nat_lit 49168964) (nat_lit 11135578240) (nat_lit 0) A10K2.u3078 from rfl, totK_node, atot3077, atot3078]
  decide +kernel

theorem arows3082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3082 = true := by
  rw [show A10K2.u3082 = KTree.node A10K2.u3080 (nat_lit 49224924) (nat_lit 4194296893) (nat_lit 0) A10K2.u3081 from rfl, allE_node, arows3080, irow3082, arows3081]
  all_goals rfl

theorem atot3082 : totK PA10K2 A10K2.u3082 = [0, 0, 1357117319707, 5718625391140, 8057337069306, 4075651183120, 546741940850, 13079907231, 0, 0] := by
  rw [show A10K2.u3082 = KTree.node A10K2.u3080 (nat_lit 49224924) (nat_lit 4194296893) (nat_lit 0) A10K2.u3081 from rfl, totK_node, atot3080, atot3081]
  decide +kernel

theorem arows3087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3087 = true := by
  rw [show A10K2.u3087 = KTree.node A10K2.u3085 (nat_lit 49244005) (nat_lit 6100788229) (nat_lit 0) A10K2.u3086 from rfl, allE_node, arows3085, irow3087, arows3086]
  all_goals rfl

theorem atot3087 : totK PA10K2 A10K2.u3087 = [0, 0, 860820066973, 4524715025824, 8117600103587, 5376958921232, 933055270360, 25936650350, 0, 0] := by
  rw [show A10K2.u3087 = KTree.node A10K2.u3085 (nat_lit 49244005) (nat_lit 6100788229) (nat_lit 0) A10K2.u3086 from rfl, totK_node, atot3085, atot3086]
  decide +kernel

theorem arows3090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3090 = true := by
  rw [show A10K2.u3090 = KTree.node A10K2.u3088 (nat_lit 49811401) (nat_lit 5872982487) (nat_lit 0) A10K2.u3089 from rfl, allE_node, arows3088, irow3090, arows3089]
  all_goals rfl

theorem atot3090 : totK PA10K2 A10K2.u3090 = [0, 1043199159673, 4734205828919, 7127668132281, 4380574793029, 1715513740595, 537746538834, 49137922124, 0, 0] := by
  rw [show A10K2.u3090 = KTree.node A10K2.u3088 (nat_lit 49811401) (nat_lit 5872982487) (nat_lit 0) A10K2.u3089 from rfl, totK_node, atot3088, atot3089]
  decide +kernel

theorem arows3094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3094 = true := by
  rw [show A10K2.u3094 = KTree.node A10K2.u3092 (nat_lit 49836332) (nat_lit 8846958634) (nat_lit 0) A10K2.u3093 from rfl, allE_node, arows3092, irow3094, arows3093]
  all_goals rfl

theorem atot3094 : totK PA10K2 A10K2.u3094 = [0, 827520024373, 4288952365048, 7819513002593, 5672934779231, 1371596205136, 83255389061, 0, 0, 0] := by
  rw [show A10K2.u3094 = KTree.node A10K2.u3092 (nat_lit 49836332) (nat_lit 8846958634) (nat_lit 0) A10K2.u3093 from rfl, totK_node, atot3092, atot3093]
  decide +kernel

theorem arows3097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3097 = true := by
  rw [show A10K2.u3097 = KTree.node A10K2.u3095 (nat_lit 49847415) (nat_lit 13510185433) (nat_lit 0) A10K2.u3096 from rfl, allE_node, arows3095, irow3097, arows3096]
  all_goals rfl

theorem atot3097 : totK PA10K2 A10K2.u3097 = [0, 0, 1348264989557, 5855830950871, 8115581916724, 3754273688416, 514976052733, 12477124820, 0, 0] := by
  rw [show A10K2.u3097 = KTree.node A10K2.u3095 (nat_lit 49847415) (nat_lit 13510185433) (nat_lit 0) A10K2.u3096 from rfl, totK_node, atot3095, atot3096]
  decide +kernel

theorem arows3103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3103 = true := by
  rw [show A10K2.u3103 = KTree.node A10K2.u3101 (nat_lit 49884672) (nat_lit 14577248077) (nat_lit 0) A10K2.u3102 from rfl, allE_node, arows3101, irow3103, arows3102]
  all_goals rfl

theorem atot3103 : totK PA10K2 A10K2.u3103 = [0, 1103809229545, 4846688688586, 7550218803951, 4937676133694, 1209437408119, 82092440535, 0, 0, 0] := by
  rw [show A10K2.u3103 = KTree.node A10K2.u3101 (nat_lit 49884672) (nat_lit 14577248077) (nat_lit 0) A10K2.u3102 from rfl, totK_node, atot3101, atot3102]
  decide +kernel

theorem arows3106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3106 = true := by
  rw [show A10K2.u3106 = KTree.node A10K2.u3104 (nat_lit 49899285) (nat_lit 6531070536) (nat_lit 0) A10K2.u3105 from rfl, allE_node, arows3104, irow3106, arows3105]
  all_goals rfl

theorem atot3106 : totK PA10K2 A10K2.u3106 = [0, 1029925566199, 5275572183271, 8500935380543, 4575866857335, 668598582227, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u3106 = KTree.node A10K2.u3104 (nat_lit 49899285) (nat_lit 6531070536) (nat_lit 0) A10K2.u3105 from rfl, totK_node, atot3104, atot3105]
  decide +kernel

theorem arows3110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3110 = true := by
  rw [show A10K2.u3110 = KTree.node A10K2.u3108 (nat_lit 49917846) (nat_lit 15959983175) (nat_lit 0) A10K2.u3109 from rfl, allE_node, arows3108, irow3110, arows3109]
  all_goals rfl

theorem atot3110 : totK PA10K2 A10K2.u3110 = [0, 0, 1249666739437, 5619563659415, 8066810258490, 3946662285558, 547512736104, 12696458652, 0, 0] := by
  rw [show A10K2.u3110 = KTree.node A10K2.u3108 (nat_lit 49917846) (nat_lit 15959983175) (nat_lit 0) A10K2.u3109 from rfl, totK_node, atot3108, atot3109]
  decide +kernel

theorem arows3113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3113 = true := by
  rw [show A10K2.u3113 = KTree.node A10K2.u3111 (nat_lit 49933716) (nat_lit 7660812700) (nat_lit 0) A10K2.u3112 from rfl, allE_node, arows3111, irow3113, arows3112]
  all_goals rfl

theorem atot3113 : totK PA10K2 A10K2.u3113 = [0, 725949308331, 3650709248280, 7021589531726, 6222595779837, 1993888629197, 127353560329, 0, 0, 0] := by
  rw [show A10K2.u3113 = KTree.node A10K2.u3111 (nat_lit 49933716) (nat_lit 7660812700) (nat_lit 0) A10K2.u3112 from rfl, totK_node, atot3111, atot3112]
  decide +kernel

theorem arows3118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3118 = true := by
  rw [show A10K2.u3118 = KTree.node A10K2.u3116 (nat_lit 50014999) (nat_lit 7574462884) (nat_lit 0) A10K2.u3117 from rfl, allE_node, arows3116, irow3118, arows3117]
  all_goals rfl

theorem atot3118 : totK PA10K2 A10K2.u3118 = [0, 878964141746, 4438744686229, 7892673342507, 5210682029902, 1012205898584, 35255389389, 0, 0, 0] := by
  rw [show A10K2.u3118 = KTree.node A10K2.u3116 (nat_lit 50014999) (nat_lit 7574462884) (nat_lit 0) A10K2.u3117 from rfl, totK_node, atot3116, atot3117]
  decide +kernel

theorem arows3121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3121 = true := by
  rw [show A10K2.u3121 = KTree.node A10K2.u3119 (nat_lit 50033043) (nat_lit 9026277603) (nat_lit 0) A10K2.u3120 from rfl, allE_node, arows3119, irow3121, arows3120]
  all_goals rfl

theorem atot3121 : totK PA10K2 A10K2.u3121 = [0, 784091755875, 4278615309301, 7820472284322, 5556548059848, 1331712146323, 80537954553, 0, 0, 0] := by
  rw [show A10K2.u3121 = KTree.node A10K2.u3119 (nat_lit 50033043) (nat_lit 9026277603) (nat_lit 0) A10K2.u3120 from rfl, totK_node, atot3119, atot3120]
  decide +kernel

theorem arows3125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3125 = true := by
  rw [show A10K2.u3125 = KTree.node A10K2.u3123 (nat_lit 50044375) (nat_lit 14298283331) (nat_lit 0) A10K2.u3124 from rfl, allE_node, arows3123, irow3125, arows3124]
  all_goals rfl

theorem atot3125 : totK PA10K2 A10K2.u3125 = [0, 0, 1204410638475, 5572164124003, 8230335942318, 4010333260736, 435056134967, 6904928264, 0, 0] := by
  rw [show A10K2.u3125 = KTree.node A10K2.u3123 (nat_lit 50044375) (nat_lit 14298283331) (nat_lit 0) A10K2.u3124 from rfl, totK_node, atot3123, atot3124]
  decide +kernel

theorem arows3128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3128 = true := by
  rw [show A10K2.u3128 = KTree.node A10K2.u3126 (nat_lit 50064833) (nat_lit 9906578028) (nat_lit 0) A10K2.u3127 from rfl, allE_node, arows3126, irow3128, arows3127]
  all_goals rfl

theorem atot3128 : totK PA10K2 A10K2.u3128 = [0, 0, 892036458401, 4615853225506, 8035420735398, 5227483206156, 967553006028, 30846741173, 0, 0] := by
  rw [show A10K2.u3128 = KTree.node A10K2.u3126 (nat_lit 50064833) (nat_lit 9906578028) (nat_lit 0) A10K2.u3127 from rfl, totK_node, atot3126, atot3127]
  decide +kernel

theorem arows3135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3135 = true := by
  rw [show A10K2.u3135 = KTree.node A10K2.u3133 (nat_lit 50074067) (nat_lit 5518991457) (nat_lit 0) A10K2.u3134 from rfl, allE_node, arows3133, irow3135, arows3134]
  all_goals rfl

theorem atot3135 : totK PA10K2 A10K2.u3135 = [0, 0, 1329250287164, 5540250941869, 7727172848879, 4091643639607, 768674624240, 49787535205, 0, 0] := by
  rw [show A10K2.u3135 = KTree.node A10K2.u3133 (nat_lit 50074067) (nat_lit 5518991457) (nat_lit 0) A10K2.u3134 from rfl, totK_node, atot3133, atot3134]
  decide +kernel

theorem arows3138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3138 = true := by
  rw [show A10K2.u3138 = KTree.node A10K2.u3136 (nat_lit 50099413) (nat_lit 4889832732) (nat_lit 0) A10K2.u3137 from rfl, allE_node, arows3136, irow3138, arows3137]
  all_goals rfl

theorem atot3138 : totK PA10K2 A10K2.u3138 = [0, 0, 537680587155, 3740663596838, 8013521635232, 6228243441462, 1433804980274, 74848461955, 0, 0] := by
  rw [show A10K2.u3138 = KTree.node A10K2.u3136 (nat_lit 50099413) (nat_lit 4889832732) (nat_lit 0) A10K2.u3137 from rfl, totK_node, atot3136, atot3137]
  decide +kernel

theorem arows3142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3142 = true := by
  rw [show A10K2.u3142 = KTree.node A10K2.u3140 (nat_lit 50127117) (nat_lit 3495430240) (nat_lit 0) A10K2.u3141 from rfl, allE_node, arows3140, irow3142, arows3141]
  all_goals rfl

theorem atot3142 : totK PA10K2 A10K2.u3142 = [0, 0, 310599358184, 2301537827574, 6483408419338, 7514667806667, 2849089458714, 299472978145, 6725424603, 0] := by
  rw [show A10K2.u3142 = KTree.node A10K2.u3140 (nat_lit 50127117) (nat_lit 3495430240) (nat_lit 0) A10K2.u3141 from rfl, totK_node, atot3140, atot3141]
  decide +kernel

theorem arows3145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3145 = true := by
  rw [show A10K2.u3145 = KTree.node A10K2.u3143 (nat_lit 50150070) (nat_lit 15054304916) (nat_lit 0) A10K2.u3144 from rfl, allE_node, arows3143, irow3145, arows3144]
  all_goals rfl

theorem atot3145 : totK PA10K2 A10K2.u3145 = [0, 0, 1205832225400, 5544131646927, 8157386451194, 4211578428189, 576525041732, 12696458652, 0, 0] := by
  rw [show A10K2.u3145 = KTree.node A10K2.u3143 (nat_lit 50150070) (nat_lit 15054304916) (nat_lit 0) A10K2.u3144 from rfl, totK_node, atot3143, atot3144]
  decide +kernel

theorem arows3150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3150 = true := by
  rw [show A10K2.u3150 = KTree.node A10K2.u3148 (nat_lit 50165235) (nat_lit 8984791200) (nat_lit 0) A10K2.u3149 from rfl, allE_node, arows3148, irow3150, arows3149]
  all_goals rfl

theorem atot3150 : totK PA10K2 A10K2.u3150 = [0, 0, 612143352615, 3814733358199, 7891276341203, 6193092641058, 1443519661228, 75083193596, 0, 0] := by
  rw [show A10K2.u3150 = KTree.node A10K2.u3148 (nat_lit 50165235) (nat_lit 8984791200) (nat_lit 0) A10K2.u3149 from rfl, totK_node, atot3148, atot3149]
  decide +kernel

theorem arows3153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3153 = true := by
  rw [show A10K2.u3153 = KTree.node A10K2.u3151 (nat_lit 50192827) (nat_lit 6453676462) (nat_lit 0) A10K2.u3152 from rfl, allE_node, arows3151, irow3153, arows3152]
  all_goals rfl

theorem atot3153 : totK PA10K2 A10K2.u3153 = [0, 0, 289498769530, 2359565358135, 6484284906446, 7323282928045, 2893228575980, 310599079433, 6860445330, 0] := by
  rw [show A10K2.u3153 = KTree.node A10K2.u3151 (nat_lit 50192827) (nat_lit 6453676462) (nat_lit 0) A10K2.u3152 from rfl, totK_node, atot3151, atot3152]
  decide +kernel

theorem arows3157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3157 = true := by
  rw [show A10K2.u3157 = KTree.node A10K2.u3155 (nat_lit 50273713) (nat_lit 9204972428) (nat_lit 0) A10K2.u3156 from rfl, allE_node, arows3155, irow3157, arows3156]
  all_goals rfl

theorem atot3157 : totK PA10K2 A10K2.u3157 = [0, 0, 1200221619159, 5497969240273, 8125197002570, 4185502427153, 525998535024, 11694325420, 0, 0] := by
  rw [show A10K2.u3157 = KTree.node A10K2.u3155 (nat_lit 50273713) (nat_lit 9204972428) (nat_lit 0) A10K2.u3156 from rfl, totK_node, atot3155, atot3156]
  decide +kernel

theorem arows3160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3160 = true := by
  rw [show A10K2.u3160 = KTree.node A10K2.u3158 (nat_lit 50293906) (nat_lit 15550823646) (nat_lit 0) A10K2.u3159 from rfl, allE_node, arows3158, irow3160, arows3159]
  all_goals rfl

theorem atot3160 : totK PA10K2 A10K2.u3160 = [0, 0, 889556536884, 4611721554183, 8121530064966, 5265717117012, 873168606060, 25571799398, 0, 0] := by
  rw [show A10K2.u3160 = KTree.node A10K2.u3158 (nat_lit 50293906) (nat_lit 15550823646) (nat_lit 0) A10K2.u3159 from rfl, totK_node, atot3158, atot3159]
  decide +kernel

theorem arows3166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3166 = true := by
  rw [show A10K2.u3166 = KTree.node A10K2.u3164 (nat_lit 50303387) (nat_lit 5205132014) (nat_lit 0) A10K2.u3165 from rfl, allE_node, arows3164, irow3166, arows3165]
  all_goals rfl

theorem atot3166 : totK PA10K2 A10K2.u3166 = [0, 0, 0, 1478600744087, 6122539595250, 8159997337557, 3335999759912, 356398198055, 6318667960, 0] := by
  rw [show A10K2.u3166 = KTree.node A10K2.u3164 (nat_lit 50303387) (nat_lit 5205132014) (nat_lit 0) A10K2.u3165 from rfl, totK_node, atot3164, atot3165]
  decide +kernel

theorem arows3169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3169 = true := by
  rw [show A10K2.u3169 = KTree.node A10K2.u3167 (nat_lit 50325218) (nat_lit 13409891128) (nat_lit 0) A10K2.u3168 from rfl, allE_node, arows3167, irow3169, arows3168]
  all_goals rfl

theorem atot3169 : totK PA10K2 A10K2.u3169 = [0, 0, 0, 877409417420, 4811229065978, 8229044807135, 4792800431492, 734408755839, 18571798697, 0] := by
  rw [show A10K2.u3169 = KTree.node A10K2.u3167 (nat_lit 50325218) (nat_lit 13409891128) (nat_lit 0) A10K2.u3168 from rfl, totK_node, atot3167, atot3168]
  decide +kernel

theorem arows3173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3173 = true := by
  rw [show A10K2.u3173 = KTree.node A10K2.u3171 (nat_lit 55127558) (nat_lit 14636515487) (nat_lit 0) A10K2.u3172 from rfl, allE_node, arows3171, irow3173, arows3172]
  all_goals rfl

theorem atot3173 : totK PA10K2 A10K2.u3173 = [0, 1023203432278, 4544868177156, 6764205886897, 3962769210994, 1401399371713, 1191999645097, 511713723036, 48886019071, 0] := by
  rw [show A10K2.u3173 = KTree.node A10K2.u3171 (nat_lit 55127558) (nat_lit 14636515487) (nat_lit 0) A10K2.u3172 from rfl, totK_node, atot3171, atot3172]
  decide +kernel

theorem arows3176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3176 = true := by
  rw [show A10K2.u3176 = KTree.node A10K2.u3174 (nat_lit 55138596) (nat_lit 14257594719) (nat_lit 0) A10K2.u3175 from rfl, allE_node, arows3174, irow3176, arows3175]
  all_goals rfl

theorem atot3176 : totK PA10K2 A10K2.u3176 = [0, 1361270744884, 5953358962279, 8204135049864, 3522011123545, 381896255971, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3176 = KTree.node A10K2.u3174 (nat_lit 55138596) (nat_lit 14257594719) (nat_lit 0) A10K2.u3175 from rfl, totK_node, atot3174, atot3175]
  decide +kernel

theorem arows3181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3181 = true := by
  rw [show A10K2.u3181 = KTree.node A10K2.u3179 (nat_lit 55158682) (nat_lit 14931092400) (nat_lit 0) A10K2.u3180 from rfl, allE_node, arows3179, irow3181, arows3180]
  all_goals rfl

theorem atot3181 : totK PA10K2 A10K2.u3181 = [0, 0, 1482602425322, 6257237303525, 8021516063952, 3346268161161, 484827715593, 25565504801, 0, 0] := by
  rw [show A10K2.u3181 = KTree.node A10K2.u3179 (nat_lit 55158682) (nat_lit 14931092400) (nat_lit 0) A10K2.u3180 from rfl, totK_node, atot3179, atot3180]
  decide +kernel

theorem arows3184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3184 = true := by
  rw [show A10K2.u3184 = KTree.node A10K2.u3182 (nat_lit 55169066) (nat_lit 6721167602) (nat_lit 0) A10K2.u3183 from rfl, allE_node, arows3182, irow3184, arows3183]
  all_goals rfl

theorem atot3184 : totK PA10K2 A10K2.u3184 = [0, 0, 1319759260243, 5643344190301, 7885765597966, 3608052335303, 450711773192, 11638555097, 0, 0] := by
  rw [show A10K2.u3184 = KTree.node A10K2.u3182 (nat_lit 55169066) (nat_lit 6721167602) (nat_lit 0) A10K2.u3183 from rfl, totK_node, atot3182, atot3183]
  decide +kernel

theorem arows3188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3188 = true := by
  rw [show A10K2.u3188 = KTree.node A10K2.u3186 (nat_lit 55187811) (nat_lit 8796516946) (nat_lit 0) A10K2.u3187 from rfl, allE_node, arows3186, irow3188, arows3187]
  all_goals rfl

theorem atot3188 : totK PA10K2 A10K2.u3188 = [0, 1228183877304, 5291571138348, 7512603888458, 4137555350230, 933620672689, 59131043721, 0, 0, 0] := by
  rw [show A10K2.u3188 = KTree.node A10K2.u3186 (nat_lit 55187811) (nat_lit 8796516946) (nat_lit 0) A10K2.u3187 from rfl, totK_node, atot3186, atot3187]
  decide +kernel

theorem arows3191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3191 = true := by
  rw [show A10K2.u3191 = KTree.node A10K2.u3189 (nat_lit 55199410) (nat_lit 14773033658) (nat_lit 0) A10K2.u3190 from rfl, allE_node, arows3189, irow3191, arows3190]
  all_goals rfl

theorem atot3191 : totK PA10K2 A10K2.u3191 = [0, 774509747268, 4295485902637, 7759427496828, 4924046323384, 895862465846, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u3191 = KTree.node A10K2.u3189 (nat_lit 55199410) (nat_lit 14773033658) (nat_lit 0) A10K2.u3190 from rfl, totK_node, atot3189, atot3190]
  decide +kernel

theorem arows3199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3199 = true := by
  rw [show A10K2.u3199 = KTree.node A10K2.u3197 (nat_lit 55225750) (nat_lit 15864890683) (nat_lit 0) A10K2.u3198 from rfl, allE_node, arows3197, irow3199, arows3198]
  all_goals rfl

theorem atot3199 : totK PA10K2 A10K2.u3199 = [0, 0, 1866677774924, 7144828014722, 7673735523134, 2004304984442, 99142531426, 0, 0, 0] := by
  rw [show A10K2.u3199 = KTree.node A10K2.u3197 (nat_lit 55225750) (nat_lit 15864890683) (nat_lit 0) A10K2.u3198 from rfl, totK_node, atot3197, atot3198]
  decide +kernel

theorem arows3202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3202 = true := by
  rw [show A10K2.u3202 = KTree.node A10K2.u3200 (nat_lit 55251410) (nat_lit 11398928849) (nat_lit 0) A10K2.u3201 from rfl, allE_node, arows3200, irow3202, arows3201]
  all_goals rfl

theorem atot3202 : totK PA10K2 A10K2.u3202 = [0, 1293755989507, 5127457956190, 7073528322687, 4566348176365, 1579517233310, 226036225137, 6354482628, 0, 0] := by
  rw [show A10K2.u3202 = KTree.node A10K2.u3200 (nat_lit 55251410) (nat_lit 11398928849) (nat_lit 0) A10K2.u3201 from rfl, totK_node, atot3200, atot3201]
  decide +kernel

theorem arows3206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3206 = true := by
  rw [show A10K2.u3206 = KTree.node A10K2.u3204 (nat_lit 55272680) (nat_lit 2507138434) (nat_lit 0) A10K2.u3205 from rfl, allE_node, arows3204, irow3206, arows3205]
  all_goals rfl

theorem atot3206 : totK PA10K2 A10K2.u3206 = [0, 836871677580, 4504499622532, 8129963927245, 5348475789151, 1015647062454, 38600540508, 0, 0, 0] := by
  rw [show A10K2.u3206 = KTree.node A10K2.u3204 (nat_lit 55272680) (nat_lit 2507138434) (nat_lit 0) A10K2.u3205 from rfl, totK_node, atot3204, atot3205]
  decide +kernel

theorem arows3209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3209 = true := by
  rw [show A10K2.u3209 = KTree.node A10K2.u3207 (nat_lit 55284230) (nat_lit 14273782330) (nat_lit 0) A10K2.u3208 from rfl, allE_node, arows3207, irow3209, arows3208]
  all_goals rfl

theorem atot3209 : totK PA10K2 A10K2.u3209 = [0, 0, 1615100965339, 6571356420368, 8357728032799, 3348425049432, 279995569679, 0, 0, 0] := by
  rw [show A10K2.u3209 = KTree.node A10K2.u3207 (nat_lit 55284230) (nat_lit 14273782330) (nat_lit 0) A10K2.u3208 from rfl, totK_node, atot3207, atot3208]
  decide +kernel

theorem arows3214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3214 = true := by
  rw [show A10K2.u3214 = KTree.node A10K2.u3212 (nat_lit 55306021) (nat_lit 6877267949) (nat_lit 0) A10K2.u3213 from rfl, allE_node, arows3212, irow3214, arows3213]
  all_goals rfl

theorem atot3214 : totK PA10K2 A10K2.u3214 = [0, 0, 836160940386, 4706263127939, 8367716544361, 5113276681814, 758128912236, 13204174009, 0, 0] := by
  rw [show A10K2.u3214 = KTree.node A10K2.u3212 (nat_lit 55306021) (nat_lit 6877267949) (nat_lit 0) A10K2.u3213 from rfl, totK_node, atot3212, atot3213]
  decide +kernel

theorem arows3217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3217 = true := by
  rw [show A10K2.u3217 = KTree.node A10K2.u3215 (nat_lit 55389908) (nat_lit 9409706037) (nat_lit 0) A10K2.u3216 from rfl, allE_node, arows3215, irow3217, arows3216]
  all_goals rfl

theorem atot3217 : totK PA10K2 A10K2.u3217 = [0, 0, 1134882974343, 4827533780003, 7372521195882, 4767636877112, 1155384877760, 73123144916, 0, 0] := by
  rw [show A10K2.u3217 = KTree.node A10K2.u3215 (nat_lit 55389908) (nat_lit 9409706037) (nat_lit 0) A10K2.u3216 from rfl, totK_node, atot3215, atot3216]
  decide +kernel

theorem arows3221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3221 = true := by
  rw [show A10K2.u3221 = KTree.node A10K2.u3219 (nat_lit 55401246) (nat_lit 4992461298) (nat_lit 0) A10K2.u3220 from rfl, allE_node, arows3219, irow3221, arows3220]
  all_goals rfl

theorem atot3221 : totK PA10K2 A10K2.u3221 = [0, 0, 1245509902467, 5756248123088, 8315911048544, 3735928435978, 394477662836, 6239673734, 0, 0] := by
  rw [show A10K2.u3221 = KTree.node A10K2.u3219 (nat_lit 55401246) (nat_lit 4992461298) (nat_lit 0) A10K2.u3220 from rfl, totK_node, atot3219, atot3220]
  decide +kernel

theorem arows3224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3224 = true := by
  rw [show A10K2.u3224 = KTree.node A10K2.u3222 (nat_lit 55421254) (nat_lit 2086060708) (nat_lit 0) A10K2.u3223 from rfl, allE_node, arows3222, irow3224, arows3223]
  all_goals rfl

theorem atot3224 : totK PA10K2 A10K2.u3224 = [0, 0, 0, 1355852183353, 5824497165349, 7807260207067, 3615459291301, 605684852121, 31018567651, 0] := by
  rw [show A10K2.u3224 = KTree.node A10K2.u3222 (nat_lit 55421254) (nat_lit 2086060708) (nat_lit 0) A10K2.u3223 from rfl, totK_node, atot3222, atot3223]
  decide +kernel

theorem arows3230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3230 = true := by
  rw [show A10K2.u3230 = KTree.node A10K2.u3228 (nat_lit 55432661) (nat_lit 5162097053) (nat_lit 0) A10K2.u3229 from rfl, allE_node, arows3228, irow3230, arows3229]
  all_goals rfl

theorem atot3230 : totK PA10K2 A10K2.u3230 = [0, 0, 166940909255, 1895461478953, 6161719937505, 7504391586720, 2885390847700, 306401515452, 5685526223, 0] := by
  rw [show A10K2.u3230 = KTree.node A10K2.u3228 (nat_lit 55432661) (nat_lit 5162097053) (nat_lit 0) A10K2.u3229 from rfl, totK_node, atot3228, atot3229]
  decide +kernel

theorem arows3233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3233 = true := by
  rw [show A10K2.u3233 = KTree.node A10K2.u3231 (nat_lit 55453773) (nat_lit 5602950333) (nat_lit 0) A10K2.u3232 from rfl, allE_node, arows3231, irow3233, arows3232]
  all_goals rfl

theorem atot3233 : totK PA10K2 A10K2.u3233 = [0, 0, 1061242968049, 5071298926420, 7942589498187, 4237961557241, 644936529049, 31195026185, 0, 0] := by
  rw [show A10K2.u3233 = KTree.node A10K2.u3231 (nat_lit 55453773) (nat_lit 5602950333) (nat_lit 0) A10K2.u3232 from rfl, totK_node, atot3231, atot3232]
  decide +kernel

theorem arows3237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3237 = true := by
  rw [show A10K2.u3237 = KTree.node A10K2.u3235 (nat_lit 55464206) (nat_lit 6652850510) (nat_lit 0) A10K2.u3236 from rfl, allE_node, arows3235, irow3237, arows3236]
  all_goals rfl

theorem atot3237 : totK PA10K2 A10K2.u3237 = [0, 0, 774509747268, 4428223410857, 7890567712914, 4618602960254, 684214692453, 23897484981, 0, 0] := by
  rw [show A10K2.u3237 = KTree.node A10K2.u3235 (nat_lit 55464206) (nat_lit 6652850510) (nat_lit 0) A10K2.u3236 from rfl, totK_node, atot3235, atot3236]
  decide +kernel

theorem arows3240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3240 = true := by
  rw [show A10K2.u3240 = KTree.node A10K2.u3238 (nat_lit 55494138) (nat_lit 12339132907) (nat_lit 0) A10K2.u3239 from rfl, allE_node, arows3238, irow3240, arows3239]
  all_goals rfl

theorem atot3240 : totK PA10K2 A10K2.u3240 = [0, 0, 187384252814, 1819983252990, 6141733887585, 7582890606853, 2649176570652, 284832294815, 6239673734, 0] := by
  rw [show A10K2.u3240 = KTree.node A10K2.u3238 (nat_lit 55494138) (nat_lit 12339132907) (nat_lit 0) A10K2.u3239 from rfl, totK_node, atot3238, atot3239]
  decide +kernel

theorem arows3245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3245 = true := by
  rw [show A10K2.u3245 = KTree.node A10K2.u3243 (nat_lit 55519392) (nat_lit 6457723451) (nat_lit 0) A10K2.u3244 from rfl, allE_node, arows3243, irow3245, arows3244]
  all_goals rfl

theorem atot3245 : totK PA10K2 A10K2.u3245 = [0, 0, 1103268677606, 5293859137443, 8299243944900, 4581667222173, 744241401124, 31285368086, 0, 0] := by
  rw [show A10K2.u3245 = KTree.node A10K2.u3243 (nat_lit 55519392) (nat_lit 6457723451) (nat_lit 0) A10K2.u3244 from rfl, totK_node, atot3243, atot3244]
  decide +kernel

theorem arows3248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3248 = true := by
  rw [show A10K2.u3248 = KTree.node A10K2.u3246 (nat_lit 55537619) (nat_lit 9178798753) (nat_lit 0) A10K2.u3247 from rfl, allE_node, arows3246, irow3248, arows3247]
  all_goals rfl

theorem atot3248 : totK PA10K2 A10K2.u3248 = [0, 292640272425, 1653873282084, 4710307281224, 7322165921619, 4915644422740, 1063183066749, 48472019145, 0, 0] := by
  rw [show A10K2.u3248 = KTree.node A10K2.u3246 (nat_lit 55537619) (nat_lit 9178798753) (nat_lit 0) A10K2.u3247 from rfl, totK_node, atot3246, atot3247]
  decide +kernel

theorem arows3252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3252 = true := by
  rw [show A10K2.u3252 = KTree.node A10K2.u3250 (nat_lit 55591744) (nat_lit 14342229915) (nat_lit 0) A10K2.u3251 from rfl, allE_node, arows3250, irow3252, arows3251]
  all_goals rfl

theorem atot3252 : totK PA10K2 A10K2.u3252 = [0, 1007158941363, 5195627945077, 8300208555160, 3945184823516, 443424416097, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u3252 = KTree.node A10K2.u3250 (nat_lit 55591744) (nat_lit 14342229915) (nat_lit 0) A10K2.u3251 from rfl, totK_node, atot3250, atot3251]
  decide +kernel

theorem arows3255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3255 = true := by
  rw [show A10K2.u3255 = KTree.node A10K2.u3253 (nat_lit 55625540) (nat_lit 12486696347) (nat_lit 0) A10K2.u3254 from rfl, allE_node, arows3253, irow3255, arows3254]
  all_goals rfl

theorem atot3255 : totK PA10K2 A10K2.u3255 = [0, 316846731414, 2317054555160, 6379471812480, 7166284557479, 2500872065839, 261494883203, 5546304973, 0, 0] := by
  rw [show A10K2.u3255 = KTree.node A10K2.u3253 (nat_lit 55625540) (nat_lit 12486696347) (nat_lit 0) A10K2.u3254 from rfl, totK_node, atot3253, atot3254]
  decide +kernel

theorem arows3262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3262 = true := by
  rw [show A10K2.u3262 = KTree.node A10K2.u3260 (nat_lit 55654634) (nat_lit 12403245268) (nat_lit 0) A10K2.u3261 from rfl, allE_node, arows3260, irow3262, arows3261]
  all_goals rfl

theorem atot3262 : totK PA10K2 A10K2.u3262 = [0, 1287679407729, 5448320861310, 7677759958361, 4072667615682, 690887243113, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3262 = KTree.node A10K2.u3260 (nat_lit 55654634) (nat_lit 12403245268) (nat_lit 0) A10K2.u3261 from rfl, totK_node, atot3260, atot3261]
  decide +kernel

theorem arows3265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3265 = true := by
  rw [show A10K2.u3265 = KTree.node A10K2.u3263 (nat_lit 55667953) (nat_lit 5803498587) (nat_lit 0) A10K2.u3264 from rfl, allE_node, arows3263, irow3265, arows3264]
  all_goals rfl

theorem atot3265 : totK PA10K2 A10K2.u3265 = [0, 592283690039, 4054393443399, 8310579671569, 5633563290762, 1167198890153, 54703720055, 0, 0, 0] := by
  rw [show A10K2.u3265 = KTree.node A10K2.u3263 (nat_lit 55667953) (nat_lit 5803498587) (nat_lit 0) A10K2.u3264 from rfl, totK_node, atot3263, atot3264]
  decide +kernel

theorem arows3269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3269 = true := by
  rw [show A10K2.u3269 = KTree.node A10K2.u3267 (nat_lit 55687316) (nat_lit 12586770762) (nat_lit 0) A10K2.u3268 from rfl, allE_node, arows3267, irow3269, arows3268]
  all_goals rfl

theorem atot3269 : totK PA10K2 A10K2.u3269 = [0, 0, 1285919446045, 5523819773815, 7734230780132, 3839400804234, 636306022355, 31082886609, 0, 0] := by
  rw [show A10K2.u3269 = KTree.node A10K2.u3267 (nat_lit 55687316) (nat_lit 12586770762) (nat_lit 0) A10K2.u3268 from rfl, totK_node, atot3267, atot3268]
  decide +kernel

theorem arows3272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3272 = true := by
  rw [show A10K2.u3272 = KTree.node A10K2.u3270 (nat_lit 55700882) (nat_lit 15078922414) (nat_lit 0) A10K2.u3271 from rfl, allE_node, arows3270, irow3272, arows3271]
  all_goals rfl

theorem atot3272 : totK PA10K2 A10K2.u3272 = [0, 582799510374, 2939218001544, 6079858110259, 6407485562755, 2741377626154, 307894617392, 6121173289, 0, 0] := by
  rw [show A10K2.u3272 = KTree.node A10K2.u3270 (nat_lit 55700882) (nat_lit 15078922414) (nat_lit 0) A10K2.u3271 from rfl, totK_node, atot3270, atot3271]
  decide +kernel

theorem arows3277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3277 = true := by
  rw [show A10K2.u3277 = KTree.node A10K2.u3275 (nat_lit 55717362) (nat_lit 14140600527) (nat_lit 0) A10K2.u3276 from rfl, allE_node, arows3275, irow3277, arows3276]
  all_goals rfl

theorem atot3277 : totK PA10K2 A10K2.u3277 = [0, 1008006057554, 4702798196938, 7612662232563, 4758437046659, 922690169048, 42529659924, 0, 0, 0] := by
  rw [show A10K2.u3277 = KTree.node A10K2.u3275 (nat_lit 55717362) (nat_lit 14140600527) (nat_lit 0) A10K2.u3276 from rfl, totK_node, atot3275, atot3276]
  decide +kernel

theorem arows3280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3280 = true := by
  rw [show A10K2.u3280 = KTree.node A10K2.u3278 (nat_lit 55728340) (nat_lit 11800462688) (nat_lit 0) A10K2.u3279 from rfl, allE_node, arows3278, irow3280, arows3279]
  all_goals rfl

theorem atot3280 : totK PA10K2 A10K2.u3280 = [0, 583317622402, 3882231725341, 7872924837548, 5348539999145, 1071151658437, 58931901996, 0, 0, 0] := by
  rw [show A10K2.u3280 = KTree.node A10K2.u3278 (nat_lit 55728340) (nat_lit 11800462688) (nat_lit 0) A10K2.u3279 from rfl, totK_node, atot3278, atot3279]
  decide +kernel

theorem arows3284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3284 = true := by
  rw [show A10K2.u3284 = KTree.node A10K2.u3282 (nat_lit 55756564) (nat_lit 13049808624) (nat_lit 0) A10K2.u3283 from rfl, allE_node, arows3282, irow3284, arows3283]
  all_goals rfl

theorem atot3284 : totK PA10K2 A10K2.u3284 = [0, 0, 1552363755479, 6238784036429, 7757524847778, 2871293725016, 334795394456, 6354482628, 0, 0] := by
  rw [show A10K2.u3284 = KTree.node A10K2.u3282 (nat_lit 55756564) (nat_lit 13049808624) (nat_lit 0) A10K2.u3283 from rfl, totK_node, atot3282, atot3283]
  decide +kernel

theorem arows3287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3287 = true := by
  rw [show A10K2.u3287 = KTree.node A10K2.u3285 (nat_lit 55853680) (nat_lit 14536470622) (nat_lit 0) A10K2.u3286 from rfl, allE_node, arows3285, irow3287, arows3286]
  all_goals rfl

theorem atot3287 : totK PA10K2 A10K2.u3287 = [0, 0, 1031233381991, 5359264753026, 8321846870613, 3708242098792, 412705028030, 5447185874, 0, 0] := by
  rw [show A10K2.u3287 = KTree.node A10K2.u3285 (nat_lit 55853680) (nat_lit 14536470622) (nat_lit 0) A10K2.u3286 from rfl, totK_node, atot3285, atot3286]
  decide +kernel

theorem arows3293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3293 = true := by
  rw [show A10K2.u3293 = KTree.node A10K2.u3291 (nat_lit 55915795) (nat_lit 10823858322) (nat_lit 0) A10K2.u3292 from rfl, allE_node, arows3291, irow3293, arows3292]
  all_goals rfl

theorem atot3293 : totK PA10K2 A10K2.u3293 = [0, 0, 1310999871876, 5406381120835, 7558578916534, 4121227934531, 762108665953, 37807056478, 0, 0] := by
  rw [show A10K2.u3293 = KTree.node A10K2.u3291 (nat_lit 55915795) (nat_lit 10823858322) (nat_lit 0) A10K2.u3292 from rfl, totK_node, atot3291, atot3292]
  decide +kernel

theorem arows3296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3296 = true := by
  rw [show A10K2.u3296 = KTree.node A10K2.u3294 (nat_lit 55928148) (nat_lit 12224751980) (nat_lit 0) A10K2.u3295 from rfl, allE_node, arows3294, irow3296, arows3295]
  all_goals rfl

theorem atot3296 : totK PA10K2 A10K2.u3296 = [0, 0, 990398109009, 5065102591344, 8354712432536, 4524479160114, 597393638983, 13317224979, 0, 0] := by
  rw [show A10K2.u3296 = KTree.node A10K2.u3294 (nat_lit 55928148) (nat_lit 12224751980) (nat_lit 0) A10K2.u3295 from rfl, totK_node, atot3294, atot3295]
  decide +kernel

theorem arows3300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3300 = true := by
  rw [show A10K2.u3300 = KTree.node A10K2.u3298 (nat_lit 55977221) (nat_lit 6792917620) (nat_lit 0) A10K2.u3299 from rfl, allE_node, arows3298, irow3300, arows3299]
  all_goals rfl

theorem atot3300 : totK PA10K2 A10K2.u3300 = [0, 0, 1246433116246, 5579683698157, 7917398962751, 3623936272298, 537224114425, 30429722018, 0, 0] := by
  rw [show A10K2.u3300 = KTree.node A10K2.u3298 (nat_lit 55977221) (nat_lit 6792917620) (nat_lit 0) A10K2.u3299 from rfl, totK_node, atot3298, atot3299]
  decide +kernel

theorem arows3303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3303 = true := by
  rw [show A10K2.u3303 = KTree.node A10K2.u3301 (nat_lit 55986412) (nat_lit 12052466929) (nat_lit 0) A10K2.u3302 from rfl, allE_node, arows3301, irow3303, arows3302]
  all_goals rfl

theorem atot3303 : totK PA10K2 A10K2.u3303 = [0, 0, 820492422360, 4518040169981, 8009523692561, 4481139352317, 678259012726, 17774690686, 0, 0] := by
  rw [show A10K2.u3303 = KTree.node A10K2.u3301 (nat_lit 55986412) (nat_lit 12052466929) (nat_lit 0) A10K2.u3302 from rfl, totK_node, atot3301, atot3302]
  decide +kernel

theorem arows3308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3308 = true := by
  rw [show A10K2.u3308 = KTree.node A10K2.u3306 (nat_lit 56017194) (nat_lit 10904646713) (nat_lit 0) A10K2.u3307 from rfl, allE_node, arows3306, irow3308, arows3307]
  all_goals rfl

theorem atot3308 : totK PA10K2 A10K2.u3308 = [0, 0, 0, 1813853921885, 7069882536612, 7451072038758, 1962685433461, 118768390350, 0, 0] := by
  rw [show A10K2.u3308 = KTree.node A10K2.u3306 (nat_lit 56017194) (nat_lit 10904646713) (nat_lit 0) A10K2.u3307 from rfl, totK_node, atot3306, atot3307]
  decide +kernel

theorem arows3311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3311 = true := by
  rw [show A10K2.u3311 = KTree.node A10K2.u3309 (nat_lit 56103538) (nat_lit 5162868806) (nat_lit 0) A10K2.u3310 from rfl, allE_node, arows3309, irow3311, arows3310]
  all_goals rfl

theorem atot3311 : totK PA10K2 A10K2.u3311 = [0, 1386233821196, 5686188786486, 7568528157583, 3543657916297, 1109223233661, 735894025269, 168882025844, 6354482628, 0] := by
  rw [show A10K2.u3311 = KTree.node A10K2.u3309 (nat_lit 56103538) (nat_lit 5162868806) (nat_lit 0) A10K2.u3310 from rfl, totK_node, atot3309, atot3310]
  decide +kernel

theorem arows3315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3315 = true := by
  rw [show A10K2.u3315 = KTree.node A10K2.u3313 (nat_lit 56132215) (nat_lit 10189420915) (nat_lit 0) A10K2.u3314 from rfl, allE_node, arows3313, irow3315, arows3314]
  all_goals rfl

theorem atot3315 : totK PA10K2 A10K2.u3315 = [0, 0, 1745019984366, 6728580579119, 8228656284016, 3203203214666, 371759277515, 7903172220, 0, 0] := by
  rw [show A10K2.u3315 = KTree.node A10K2.u3313 (nat_lit 56132215) (nat_lit 10189420915) (nat_lit 0) A10K2.u3314 from rfl, totK_node, atot3313, atot3314]
  decide +kernel

theorem arows3318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3318 = true := by
  rw [show A10K2.u3318 = KTree.node A10K2.u3316 (nat_lit 56175268) (nat_lit 13583629385) (nat_lit 0) A10K2.u3317 from rfl, allE_node, arows3316, irow3318, arows3317]
  all_goals rfl

theorem atot3318 : totK PA10K2 A10K2.u3318 = [0, 846901670217, 4268457654229, 7650234015125, 5577101745398, 1406297159946, 89319918621, 0, 0, 0] := by
  rw [show A10K2.u3318 = KTree.node A10K2.u3316 (nat_lit 56175268) (nat_lit 13583629385) (nat_lit 0) A10K2.u3317 from rfl, totK_node, atot3316, atot3317]
  decide +kernel

theorem arows3327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3327 = true := by
  rw [show A10K2.u3327 = KTree.node A10K2.u3325 (nat_lit 56187669) (nat_lit 7018395041) (nat_lit 0) A10K2.u3326 from rfl, allE_node, arows3325, irow3327, arows3326]
  all_goals rfl

theorem atot3327 : totK PA10K2 A10K2.u3327 = [0, 1371842486777, 5898024555612, 8219730367956, 3809170479346, 447571867834, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3327 = KTree.node A10K2.u3325 (nat_lit 56187669) (nat_lit 7018395041) (nat_lit 0) A10K2.u3326 from rfl, totK_node, atot3325, atot3326]
  decide +kernel

theorem arows3330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3330 = true := by
  rw [show A10K2.u3330 = KTree.node A10K2.u3328 (nat_lit 56207468) (nat_lit 11394077781) (nat_lit 0) A10K2.u3329 from rfl, allE_node, arows3328, irow3330, arows3329]
  all_goals rfl

theorem atot3330 : totK PA10K2 A10K2.u3330 = [0, 0, 1459405248901, 5995409415519, 7951894615552, 3608583779496, 533846583072, 25565504801, 0, 0] := by
  rw [show A10K2.u3330 = KTree.node A10K2.u3328 (nat_lit 56207468) (nat_lit 11394077781) (nat_lit 0) A10K2.u3329 from rfl, totK_node, atot3328, atot3329]
  decide +kernel

theorem arows3334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3334 = true := by
  rw [show A10K2.u3334 = KTree.node A10K2.u3332 (nat_lit 56219930) (nat_lit 13440627783) (nat_lit 0) A10K2.u3333 from rfl, allE_node, arows3332, irow3334, arows3333]
  all_goals rfl

theorem atot3334 : totK PA10K2 A10K2.u3334 = [0, 106966390865, 1590442496821, 5947382461989, 7909601189005, 3488821033405, 440536190636, 11638555097, 0, 0] := by
  rw [show A10K2.u3334 = KTree.node A10K2.u3332 (nat_lit 56219930) (nat_lit 13440627783) (nat_lit 0) A10K2.u3333 from rfl, totK_node, atot3332, atot3333]
  decide +kernel

theorem arows3337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3337 = true := by
  rw [show A10K2.u3337 = KTree.node A10K2.u3335 (nat_lit 56303026) (nat_lit 13770425449) (nat_lit 0) A10K2.u3336 from rfl, allE_node, arows3335, irow3337, arows3336]
  all_goals rfl

theorem atot3337 : totK PA10K2 A10K2.u3337 = [0, 1303945051267, 5894575873263, 8416741903402, 3960316182527, 497405793064, 13360781053, 0, 0, 0] := by
  rw [show A10K2.u3337 = KTree.node A10K2.u3335 (nat_lit 56303026) (nat_lit 13770425449) (nat_lit 0) A10K2.u3336 from rfl, totK_node, atot3335, atot3336]
  decide +kernel

theorem arows3342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3342 = true := by
  rw [show A10K2.u3342 = KTree.node A10K2.u3340 (nat_lit 56321920) (nat_lit 14332185212) (nat_lit 0) A10K2.u3341 from rfl, allE_node, arows3340, irow3342, arows3341]
  all_goals rfl

theorem atot3342 : totK PA10K2 A10K2.u3342 = [0, 873803232168, 4441649072624, 7892696736107, 5406349671623, 1096941583338, 45493318729, 0, 0, 0] := by
  rw [show A10K2.u3342 = KTree.node A10K2.u3340 (nat_lit 56321920) (nat_lit 14332185212) (nat_lit 0) A10K2.u3341 from rfl, totK_node, atot3340, atot3341]
  decide +kernel

theorem arows3345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3345 = true := by
  rw [show A10K2.u3345 = KTree.node A10K2.u3343 (nat_lit 56332759) (nat_lit 13855050399) (nat_lit 0) A10K2.u3344 from rfl, allE_node, arows3343, irow3345, arows3344]
  all_goals rfl

theorem atot3345 : totK PA10K2 A10K2.u3345 = [0, 0, 1530693316820, 6345001024761, 8267392414612, 3495240178474, 382214486373, 6904928264, 0, 0] := by
  rw [show A10K2.u3345 = KTree.node A10K2.u3343 (nat_lit 56332759) (nat_lit 13855050399) (nat_lit 0) A10K2.u3344 from rfl, totK_node, atot3343, atot3344]
  decide +kernel

theorem arows3349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3349 = true := by
  rw [show A10K2.u3349 = KTree.node A10K2.u3347 (nat_lit 56354259) (nat_lit 10572348480) (nat_lit 0) A10K2.u3348 from rfl, allE_node, arows3347, irow3349, arows3348]
  all_goals rfl

theorem atot3349 : totK PA10K2 A10K2.u3349 = [0, 0, 872513974627, 4705322877313, 8257248068468, 5078383390958, 798329678249, 19271132487, 0, 0] := by
  rw [show A10K2.u3349 = KTree.node A10K2.u3347 (nat_lit 56354259) (nat_lit 10572348480) (nat_lit 0) A10K2.u3348 from rfl, totK_node, atot3347, atot3348]
  decide +kernel

theorem arows3352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3352 = true := by
  rw [show A10K2.u3352 = KTree.node A10K2.u3350 (nat_lit 56365412) (nat_lit 13219278247) (nat_lit 0) A10K2.u3351 from rfl, allE_node, arows3350, irow3352, arows3351]
  all_goals rfl

theorem atot3352 : totK PA10K2 A10K2.u3352 = [0, 0, 1384231194985, 5771585415504, 8014367486412, 4260242342744, 879633684057, 56789191291, 0, 0] := by
  rw [show A10K2.u3352 = KTree.node A10K2.u3350 (nat_lit 56365412) (nat_lit 13219278247) (nat_lit 0) A10K2.u3351 from rfl, totK_node, atot3350, atot3351]
  decide +kernel

theorem arows3358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3358 = true := by
  rw [show A10K2.u3358 = KTree.node A10K2.u3356 (nat_lit 56394168) (nat_lit 14561152950) (nat_lit 0) A10K2.u3357 from rfl, allE_node, arows3356, irow3358, arows3357]
  all_goals rfl

theorem atot3358 : totK PA10K2 A10K2.u3358 = [0, 0, 0, 2348522861490, 8114307357949, 8000058015448, 1995484872917, 97078384624, 0, 0] := by
  rw [show A10K2.u3358 = KTree.node A10K2.u3356 (nat_lit 56394168) (nat_lit 14561152950) (nat_lit 0) A10K2.u3357 from rfl, totK_node, atot3356, atot3357]
  decide +kernel

theorem arows3361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3361 = true := by
  rw [show A10K2.u3361 = KTree.node A10K2.u3359 (nat_lit 56440128) (nat_lit 3369714946) (nat_lit 0) A10K2.u3360 from rfl, allE_node, arows3359, irow3361, arows3360]
  all_goals rfl

theorem atot3361 : totK PA10K2 A10K2.u3361 = [0, 0, 1323561668771, 5450303412590, 7622753441315, 4171009548681, 889977866445, 68981838711, 0, 0] := by
  rw [show A10K2.u3361 = KTree.node A10K2.u3359 (nat_lit 56440128) (nat_lit 3369714946) (nat_lit 0) A10K2.u3360 from rfl, totK_node, atot3359, atot3360]
  decide +kernel

theorem arows3365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3365 = true := by
  rw [show A10K2.u3365 = KTree.node A10K2.u3363 (nat_lit 56452965) (nat_lit 6560174483) (nat_lit 0) A10K2.u3364 from rfl, allE_node, arows3363, irow3365, arows3364]
  all_goals rfl

theorem atot3365 : totK PA10K2 A10K2.u3365 = [0, 0, 895182488223, 4883579624038, 8426127104529, 4941066541664, 746847896923, 13202416085, 0, 0] := by
  rw [show A10K2.u3365 = KTree.node A10K2.u3363 (nat_lit 56452965) (nat_lit 6560174483) (nat_lit 0) A10K2.u3364 from rfl, totK_node, atot3363, atot3364]
  decide +kernel

theorem arows3368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3368 = true := by
  rw [show A10K2.u3368 = KTree.node A10K2.u3366 (nat_lit 56471551) (nat_lit 12669053876) (nat_lit 0) A10K2.u3367 from rfl, allE_node, arows3366, irow3368, arows3367]
  all_goals rfl

theorem atot3368 : totK PA10K2 A10K2.u3368 = [0, 0, 0, 1597092720345, 6290483541878, 7861355371212, 3281213696177, 383409527424, 7151180950, 0] := by
  rw [show A10K2.u3368 = KTree.node A10K2.u3366 (nat_lit 56471551) (nat_lit 12669053876) (nat_lit 0) A10K2.u3367 from rfl, totK_node, atot3366, atot3367]
  decide +kernel

theorem arows3373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3373 = true := by
  rw [show A10K2.u3373 = KTree.node A10K2.u3371 (nat_lit 56559735) (nat_lit 14004389114) (nat_lit 0) A10K2.u3372 from rfl, allE_node, arows3371, irow3373, arows3372]
  all_goals rfl

theorem atot3373 : totK PA10K2 A10K2.u3373 = [0, 0, 927708215146, 4459409481610, 7821634756366, 5680619118534, 1328309195647, 62533990090, 0, 0] := by
  rw [show A10K2.u3373 = KTree.node A10K2.u3371 (nat_lit 56559735) (nat_lit 14004389114) (nat_lit 0) A10K2.u3372 from rfl, totK_node, atot3371, atot3372]
  decide +kernel

theorem arows3376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3376 = true := by
  rw [show A10K2.u3376 = KTree.node A10K2.u3374 (nat_lit 56572700) (nat_lit 11740237283) (nat_lit 0) A10K2.u3375 from rfl, allE_node, arows3374, irow3376, arows3375]
  all_goals rfl

theorem atot3376 : totK PA10K2 A10K2.u3376 = [0, 0, 1355511981614, 5826192909590, 8126546697565, 4010131362958, 537699630252, 12219140272, 0, 0] := by
  rw [show A10K2.u3376 = KTree.node A10K2.u3374 (nat_lit 56572700) (nat_lit 11740237283) (nat_lit 0) A10K2.u3375 from rfl, totK_node, atot3374, atot3375]
  decide +kernel

theorem arows3380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3380 = true := by
  rw [show A10K2.u3380 = KTree.node A10K2.u3378 (nat_lit 56590728) (nat_lit 14332909434) (nat_lit 0) A10K2.u3379 from rfl, allE_node, arows3378, irow3380, arows3379]
  all_goals rfl

theorem atot3380 : totK PA10K2 A10K2.u3380 = [0, 0, 0, 1915807340120, 7294093417622, 8071181870969, 2629362997485, 192997072903, 0, 0] := by
  rw [show A10K2.u3380 = KTree.node A10K2.u3378 (nat_lit 56590728) (nat_lit 14332909434) (nat_lit 0) A10K2.u3379 from rfl, totK_node, atot3378, atot3379]
  decide +kernel

theorem arows3383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3383 = true := by
  rw [show A10K2.u3383 = KTree.node A10K2.u3381 (nat_lit 56614984) (nat_lit 13784267902) (nat_lit 0) A10K2.u3382 from rfl, allE_node, arows3381, irow3383, arows3382]
  all_goals rfl

theorem atot3383 : totK PA10K2 A10K2.u3383 = [0, 0, 0, 1345682477297, 5966971544441, 8355063575913, 3843426015287, 397844551669, 6439430839, 0] := by
  rw [show A10K2.u3383 = KTree.node A10K2.u3381 (nat_lit 56614984) (nat_lit 13784267902) (nat_lit 0) A10K2.u3382 from rfl, totK_node, atot3381, atot3382]
  decide +kernel

theorem arows3390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3390 = true := by
  rw [show A10K2.u3390 = KTree.node A10K2.u3388 (nat_lit 57223429) (nat_lit 6931594791) (nat_lit 0) A10K2.u3389 from rfl, allE_node, arows3388, irow3390, arows3389]
  all_goals rfl

theorem atot3390 : totK PA10K2 A10K2.u3390 = [0, 0, 873090004754, 3779076674118, 6149786399873, 5141932665677, 2768523059576, 708789415658, 41875219570, 0] := by
  rw [show A10K2.u3390 = KTree.node A10K2.u3388 (nat_lit 57223429) (nat_lit 6931594791) (nat_lit 0) A10K2.u3389 from rfl, totK_node, atot3388, atot3389]
  decide +kernel

theorem arows3393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3393 = true := by
  rw [show A10K2.u3393 = KTree.node A10K2.u3391 (nat_lit 57233735) (nat_lit 1190110858) (nat_lit 0) A10K2.u3392 from rfl, allE_node, arows3391, irow3393, arows3392]
  all_goals rfl

theorem atot3393 : totK PA10K2 A10K2.u3393 = [0, 0, 1453414764638, 5917299015387, 7796954847226, 3439353289935, 442244044993, 12388698189, 0, 0] := by
  rw [show A10K2.u3393 = KTree.node A10K2.u3391 (nat_lit 57233735) (nat_lit 1190110858) (nat_lit 0) A10K2.u3392 from rfl, totK_node, atot3391, atot3392]
  decide +kernel

theorem arows3397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3397 = true := by
  rw [show A10K2.u3397 = KTree.node A10K2.u3395 (nat_lit 57255126) (nat_lit 14901031802) (nat_lit 0) A10K2.u3396 from rfl, allE_node, arows3395, irow3397, arows3396]
  all_goals rfl

theorem atot3397 : totK PA10K2 A10K2.u3397 = [0, 0, 45770322325, 2170928212560, 7345017212339, 7711621581784, 2341453429945, 148686025421, 0, 0] := by
  rw [show A10K2.u3397 = KTree.node A10K2.u3395 (nat_lit 57255126) (nat_lit 14901031802) (nat_lit 0) A10K2.u3396 from rfl, totK_node, atot3395, atot3396]
  decide +kernel

theorem arows3400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3400 = true := by
  rw [show A10K2.u3400 = KTree.node A10K2.u3398 (nat_lit 57264204) (nat_lit 10866111231) (nat_lit 0) A10K2.u3399 from rfl, allE_node, arows3398, irow3400, arows3399]
  all_goals rfl

theorem atot3400 : totK PA10K2 A10K2.u3400 = [0, 0, 0, 1190548677740, 5137309303766, 7466044806173, 4034272712190, 754524428935, 37204059898, 0] := by
  rw [show A10K2.u3400 = KTree.node A10K2.u3398 (nat_lit 57264204) (nat_lit 10866111231) (nat_lit 0) A10K2.u3399 from rfl, totK_node, atot3398, atot3399]
  decide +kernel

theorem arows3405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3405 = true := by
  rw [show A10K2.u3405 = KTree.node A10K2.u3403 (nat_lit 57284642) (nat_lit 8448699946) (nat_lit 0) A10K2.u3404 from rfl, allE_node, arows3403, irow3405, arows3404]
  all_goals rfl

theorem atot3405 : totK PA10K2 A10K2.u3405 = [0, 0, 1225039579208, 5186937156105, 7407283160014, 4250264191200, 1020945122766, 73090668190, 0, 0] := by
  rw [show A10K2.u3405 = KTree.node A10K2.u3403 (nat_lit 57284642) (nat_lit 8448699946) (nat_lit 0) A10K2.u3404 from rfl, totK_node, atot3403, atot3404]
  decide +kernel

theorem arows3408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3408 = true := by
  rw [show A10K2.u3408 = KTree.node A10K2.u3406 (nat_lit 57296150) (nat_lit 10514083603) (nat_lit 0) A10K2.u3407 from rfl, allE_node, arows3406, irow3408, arows3407]
  all_goals rfl

theorem atot3408 : totK PA10K2 A10K2.u3408 = [0, 0, 773611290687, 4370805932131, 7941134239396, 4823540898276, 793109821087, 31768748853, 0, 0] := by
  rw [show A10K2.u3408 = KTree.node A10K2.u3406 (nat_lit 57296150) (nat_lit 10514083603) (nat_lit 0) A10K2.u3407 from rfl, totK_node, atot3406, atot3407]
  decide +kernel

theorem arows3412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3412 = true := by
  rw [show A10K2.u3412 = KTree.node A10K2.u3410 (nat_lit 57322324) (nat_lit 12885796294) (nat_lit 0) A10K2.u3411 from rfl, allE_node, arows3410, irow3412, arows3411]
  all_goals rfl

theorem atot3412 : totK PA10K2 A10K2.u3412 = [0, 0, 0, 1989585900265, 7320785642534, 7534272213439, 1799699519232, 94749165966, 0, 0] := by
  rw [show A10K2.u3412 = KTree.node A10K2.u3410 (nat_lit 57322324) (nat_lit 12885796294) (nat_lit 0) A10K2.u3411 from rfl, totK_node, atot3410, atot3411]
  decide +kernel

theorem arows3415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3415 = true := by
  rw [show A10K2.u3415 = KTree.node A10K2.u3413 (nat_lit 57351558) (nat_lit 15938083347) (nat_lit 0) A10K2.u3414 from rfl, allE_node, arows3413, irow3415, arows3414]
  all_goals rfl

theorem atot3415 : totK PA10K2 A10K2.u3415 = [0, 0, 1290752091112, 5135141826991, 7054787881547, 4499607229207, 1508249286017, 208241182707, 6354482628, 0] := by
  rw [show A10K2.u3415 = KTree.node A10K2.u3413 (nat_lit 57351558) (nat_lit 15938083347) (nat_lit 0) A10K2.u3414 from rfl, totK_node, atot3413, atot3414]
  decide +kernel

theorem arows3421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3421 = true := by
  rw [show A10K2.u3421 = KTree.node A10K2.u3419 (nat_lit 57370496) (nat_lit 13745788333) (nat_lit 0) A10K2.u3420 from rfl, allE_node, arows3419, irow3421, arows3420]
  all_goals rfl

theorem atot3421 : totK PA10K2 A10K2.u3421 = [0, 0, 834905328705, 4467598918087, 8131435839739, 5514342594376, 1047613483856, 38709934851, 0, 0] := by
  rw [show A10K2.u3421 = KTree.node A10K2.u3419 (nat_lit 57370496) (nat_lit 13745788333) (nat_lit 0) A10K2.u3420 from rfl, totK_node, atot3419, atot3420]
  decide +kernel

theorem arows3424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3424 = true := by
  rw [show A10K2.u3424 = KTree.node A10K2.u3422 (nat_lit 57387816) (nat_lit 8429457519) (nat_lit 0) A10K2.u3423 from rfl, allE_node, arows3422, irow3424, arows3423]
  all_goals rfl

theorem atot3424 : totK PA10K2 A10K2.u3424 = [0, 0, 0, 1512909740820, 6289189829606, 8153917341345, 3646508256544, 417144034020, 7047025452, 0] := by
  rw [show A10K2.u3424 = KTree.node A10K2.u3422 (nat_lit 57387816) (nat_lit 8429457519) (nat_lit 0) A10K2.u3423 from rfl, totK_node, atot3422, atot3423]
  decide +kernel

theorem arows3428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3428 = true := by
  rw [show A10K2.u3428 = KTree.node A10K2.u3426 (nat_lit 57408627) (nat_lit 6088182525) (nat_lit 0) A10K2.u3427 from rfl, allE_node, arows3426, irow3428, arows3427]
  all_goals rfl

theorem atot3428 : totK PA10K2 A10K2.u3428 = [0, 0, 0, 1479008410768, 6044083485038, 7872551546790, 3703033293255, 629185397479, 35748683383, 0] := by
  rw [show A10K2.u3428 = KTree.node A10K2.u3426 (nat_lit 57408627) (nat_lit 6088182525) (nat_lit 0) A10K2.u3427 from rfl, totK_node, atot3426, atot3427]
  decide +kernel

theorem arows3431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3431 = true := by
  rw [show A10K2.u3431 = KTree.node A10K2.u3429 (nat_lit 57492640) (nat_lit 7553700129) (nat_lit 0) A10K2.u3430 from rfl, allE_node, arows3429, irow3431, arows3430]
  all_goals rfl

theorem atot3431 : totK PA10K2 A10K2.u3431 = [0, 0, 0, 718622367072, 4407906303242, 8094065133824, 4703327187888, 754179977404, 31768748853, 0] := by
  rw [show A10K2.u3431 = KTree.node A10K2.u3429 (nat_lit 57492640) (nat_lit 7553700129) (nat_lit 0) A10K2.u3430 from rfl, totK_node, atot3429, atot3430]
  decide +kernel

theorem arows3436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3436 = true := by
  rw [show A10K2.u3436 = KTree.node A10K2.u3434 (nat_lit 57505236) (nat_lit 8574041929) (nat_lit 0) A10K2.u3435 from rfl, allE_node, arows3434, irow3436, arows3435]
  all_goals rfl

theorem atot3436 : totK PA10K2 A10K2.u3436 = [0, 0, 0, 777446694424, 4147734515521, 7741035770509, 5600584058184, 1299881665995, 74350104470, 0] := by
  rw [show A10K2.u3436 = KTree.node A10K2.u3434 (nat_lit 57505236) (nat_lit 8574041929) (nat_lit 0) A10K2.u3435 from rfl, totK_node, atot3434, atot3435]
  decide +kernel

theorem arows3439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3439 = true := by
  rw [show A10K2.u3439 = KTree.node A10K2.u3437 (nat_lit 57524581) (nat_lit 7278552219) (nat_lit 0) A10K2.u3438 from rfl, allE_node, arows3437, irow3439, arows3438]
  all_goals rfl

theorem atot3439 : totK PA10K2 A10K2.u3439 = [0, 0, 0, 0, 908287188961, 4972007751445, 7854471931178, 4014308942512, 656174681934, 31018567651] := by
  rw [show A10K2.u3439 = KTree.node A10K2.u3437 (nat_lit 57524581) (nat_lit 7278552219) (nat_lit 0) A10K2.u3438 from rfl, totK_node, atot3437, atot3438]
  decide +kernel

theorem arows3443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3443 = true := by
  rw [show A10K2.u3443 = KTree.node A10K2.u3441 (nat_lit 57542949) (nat_lit 7473810852) (nat_lit 0) A10K2.u3442 from rfl, allE_node, arows3441, irow3443, arows3442]
  all_goals rfl

theorem atot3443 : totK PA10K2 A10K2.u3443 = [0, 0, 0, 1047676262739, 4855505668742, 7364988948533, 4219272739830, 1166064022886, 171282463617, 5685526223] := by
  rw [show A10K2.u3443 = KTree.node A10K2.u3441 (nat_lit 57542949) (nat_lit 7473810852) (nat_lit 0) A10K2.u3442 from rfl, totK_node, atot3441, atot3442]
  decide +kernel

theorem arows3446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3446 = true := by
  rw [show A10K2.u3446 = KTree.node A10K2.u3444 (nat_lit 57557444) (nat_lit 9052300055) (nat_lit 0) A10K2.u3445 from rfl, allE_node, arows3444, irow3446, arows3445]
  all_goals rfl

theorem atot3446 : totK PA10K2 A10K2.u3446 = [0, 0, 0, 946910246213, 4938709611361, 7946536646405, 4251136794497, 694910572243, 31768748853, 0] := by
  rw [show A10K2.u3446 = KTree.node A10K2.u3444 (nat_lit 57557444) (nat_lit 9052300055) (nat_lit 0) A10K2.u3445 from rfl, totK_node, atot3444, atot3445]
  decide +kernel

theorem arows3454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3454 = true := by
  rw [show A10K2.u3454 = KTree.node A10K2.u3452 (nat_lit 57584275) (nat_lit 10905626811) (nat_lit 0) A10K2.u3453 from rfl, allE_node, arows3452, irow3454, arows3453]
  all_goals rfl

theorem atot3454 : totK PA10K2 A10K2.u3454 = [0, 0, 0, 0, 2153004445827, 7659215756184, 7134061865214, 1628383744987, 89016554963, 0] := by
  rw [show A10K2.u3454 = KTree.node A10K2.u3452 (nat_lit 57584275) (nat_lit 10905626811) (nat_lit 0) A10K2.u3453 from rfl, totK_node, atot3452, atot3453]
  decide +kernel

theorem arows3457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3457 = true := by
  rw [show A10K2.u3457 = KTree.node A10K2.u3455 (nat_lit 57616132) (nat_lit 10566535685) (nat_lit 0) A10K2.u3456 from rfl, allE_node, arows3455, irow3457, arows3456]
  all_goals rfl

theorem atot3457 : totK PA10K2 A10K2.u3457 = [0, 0, 0, 1287648500790, 5008945872971, 6903414519308, 4588710181994, 1499243302791, 208248089560, 5982052406] := by
  rw [show A10K2.u3457 = KTree.node A10K2.u3455 (nat_lit 57616132) (nat_lit 10566535685) (nat_lit 0) A10K2.u3456 from rfl, totK_node, atot3455, atot3456]
  decide +kernel

theorem arows3461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3461 = true := by
  rw [show A10K2.u3461 = KTree.node A10K2.u3459 (nat_lit 57636012) (nat_lit 10297731161) (nat_lit 0) A10K2.u3460 from rfl, allE_node, arows3459, irow3461, arows3460]
  all_goals rfl

theorem atot3461 : totK PA10K2 A10K2.u3461 = [0, 0, 559138620308, 2738271654958, 5787491104786, 6676393588543, 3546099746930, 678468580849, 36702257158, 0] := by
  rw [show A10K2.u3461 = KTree.node A10K2.u3459 (nat_lit 57636012) (nat_lit 10297731161) (nat_lit 0) A10K2.u3460 from rfl, totK_node, atot3459, atot3460]
  decide +kernel

theorem arows3464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3464 = true := by
  rw [show A10K2.u3464 = KTree.node A10K2.u3462 (nat_lit 57690274) (nat_lit 13527284891) (nat_lit 0) A10K2.u3463 from rfl, allE_node, arows3462, irow3464, arows3463]
  all_goals rfl

theorem atot3464 : totK PA10K2 A10K2.u3464 = [0, 0, 738817371650, 4492965109380, 8271521433703, 4651090236855, 685562611344, 17206429534, 0, 0] := by
  rw [show A10K2.u3464 = KTree.node A10K2.u3462 (nat_lit 57690274) (nat_lit 13527284891) (nat_lit 0) A10K2.u3463 from rfl, totK_node, atot3462, atot3463]
  decide +kernel

theorem arows3469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3469 = true := by
  rw [show A10K2.u3469 = KTree.node A10K2.u3467 (nat_lit 57725283) (nat_lit 5436723824) (nat_lit 0) A10K2.u3468 from rfl, allE_node, arows3467, irow3469, arows3468]
  all_goals rfl

theorem atot3469 : totK PA10K2 A10K2.u3469 = [0, 0, 756252033968, 3457871759630, 6643120468945, 6014296851947, 1807681474275, 160773292252, 5546304973, 0] := by
  rw [show A10K2.u3469 = KTree.node A10K2.u3467 (nat_lit 57725283) (nat_lit 5436723824) (nat_lit 0) A10K2.u3468 from rfl, totK_node, atot3467, atot3468]
  decide +kernel

theorem arows3472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3472 = true := by
  rw [show A10K2.u3472 = KTree.node A10K2.u3470 (nat_lit 57753957) (nat_lit 7278552219) (nat_lit 0) A10K2.u3471 from rfl, allE_node, arows3470, irow3472, arows3471]
  all_goals rfl

theorem atot3472 : totK PA10K2 A10K2.u3472 = [0, 0, 843822233352, 4759792769559, 8162757927030, 4563533222783, 722663940922, 31768748853, 0, 0] := by
  rw [show A10K2.u3472 = KTree.node A10K2.u3470 (nat_lit 57753957) (nat_lit 7278552219) (nat_lit 0) A10K2.u3471 from rfl, totK_node, atot3470, atot3471]
  decide +kernel

theorem arows3476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3476 = true := by
  rw [show A10K2.u3476 = KTree.node A10K2.u3474 (nat_lit 57767724) (nat_lit 12259685948) (nat_lit 0) A10K2.u3475 from rfl, allE_node, arows3474, irow3476, arows3475]
  all_goals rfl

theorem atot3476 : totK PA10K2 A10K2.u3476 = [0, 0, 588004983511, 3660859897338, 7834302064414, 6129092485317, 1406835780078, 75580272449, 0, 0] := by
  rw [show A10K2.u3476 = KTree.node A10K2.u3474 (nat_lit 57767724) (nat_lit 12259685948) (nat_lit 0) A10K2.u3475 from rfl, totK_node, atot3474, atot3475]
  decide +kernel

theorem arows3479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3479 = true := by
  rw [show A10K2.u3479 = KTree.node A10K2.u3477 (nat_lit 57787549) (nat_lit 6181965923) (nat_lit 0) A10K2.u3478 from rfl, allE_node, arows3477, irow3479, arows3478]
  all_goals rfl

theorem atot3479 : totK PA10K2 A10K2.u3479 = [0, 0, 0, 760216663665, 4633231386141, 8280776828110, 4431059010358, 693992482985, 31082886609, 0] := by
  rw [show A10K2.u3479 = KTree.node A10K2.u3477 (nat_lit 57787549) (nat_lit 6181965923) (nat_lit 0) A10K2.u3478 from rfl, totK_node, atot3477, atot3478]
  decide +kernel

theorem arows3485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3485 = true := by
  rw [show A10K2.u3485 = KTree.node A10K2.u3483 (nat_lit 57805029) (nat_lit 7148711552) (nat_lit 0) A10K2.u3484 from rfl, allE_node, arows3483, irow3485, arows3484]
  all_goals rfl

theorem atot3485 : totK PA10K2 A10K2.u3485 = [0, 0, 882438055320, 4287587046790, 7338980565001, 4927668978922, 1429293930437, 191434457786, 6121173289, 0] := by
  rw [show A10K2.u3485 = KTree.node A10K2.u3483 (nat_lit 57805029) (nat_lit 7148711552) (nat_lit 0) A10K2.u3484 from rfl, totK_node, atot3483, atot3484]
  decide +kernel

theorem arows3488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3488 = true := by
  rw [show A10K2.u3488 = KTree.node A10K2.u3486 (nat_lit 57817778) (nat_lit 14666697559) (nat_lit 0) A10K2.u3487 from rfl, allE_node, arows3486, irow3488, arows3487]
  all_goals rfl

theorem atot3488 : totK PA10K2 A10K2.u3488 = [0, 0, 1289468480277, 5536957185722, 7710094192659, 3901552014291, 664067056124, 31768748853, 0, 0] := by
  rw [show A10K2.u3488 = KTree.node A10K2.u3486 (nat_lit 57817778) (nat_lit 14666697559) (nat_lit 0) A10K2.u3487 from rfl, totK_node, atot3486, atot3487]
  decide +kernel

theorem arows3492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3492 = true := by
  rw [show A10K2.u3492 = KTree.node A10K2.u3490 (nat_lit 57838238) (nat_lit 7948111138) (nat_lit 0) A10K2.u3491 from rfl, allE_node, arows3490, irow3492, arows3491]
  all_goals rfl

theorem atot3492 : totK PA10K2 A10K2.u3492 = [0, 0, 0, 2401239571466, 7941965309385, 6964018616296, 1447275007612, 57439356141, 0, 0] := by
  rw [show A10K2.u3492 = KTree.node A10K2.u3490 (nat_lit 57838238) (nat_lit 7948111138) (nat_lit 0) A10K2.u3491 from rfl, totK_node, atot3490, atot3491]
  decide +kernel

theorem arows3495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3495 = true := by
  rw [show A10K2.u3495 = KTree.node A10K2.u3493 (nat_lit 57858210) (nat_lit 13819295043) (nat_lit 0) A10K2.u3494 from rfl, allE_node, arows3493, irow3495, arows3494]
  all_goals rfl

theorem atot3495 : totK PA10K2 A10K2.u3495 = [0, 0, 0, 1455040294515, 6155748520535, 7916554652214, 2758093926187, 293611364336, 6354482628, 0] := by
  rw [show A10K2.u3495 = KTree.node A10K2.u3493 (nat_lit 57858210) (nat_lit 13819295043) (nat_lit 0) A10K2.u3494 from rfl, totK_node, atot3493, atot3494]
  decide +kernel

theorem arows3500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3500 = true := by
  rw [show A10K2.u3500 = KTree.node A10K2.u3498 (nat_lit 58008818) (nat_lit 15077020812) (nat_lit 0) A10K2.u3499 from rfl, allE_node, arows3498, irow3500, arows3499]
  all_goals rfl

theorem atot3500 : totK PA10K2 A10K2.u3500 = [0, 0, 0, 1258909157114, 5779853935188, 8218633964513, 3457557845769, 330386069356, 6354482628, 0] := by
  rw [show A10K2.u3500 = KTree.node A10K2.u3498 (nat_lit 58008818) (nat_lit 15077020812) (nat_lit 0) A10K2.u3499 from rfl, totK_node, atot3498, atot3499]
  decide +kernel

theorem arows3503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3503 = true := by
  rw [show A10K2.u3503 = KTree.node A10K2.u3501 (nat_lit 58017864) (nat_lit 12619673697) (nat_lit 0) A10K2.u3502 from rfl, allE_node, arows3501, irow3503, arows3502]
  all_goals rfl

theorem atot3503 : totK PA10K2 A10K2.u3503 = [0, 0, 0, 1056956378585, 4976103039996, 7777110253684, 4264061739989, 755086750022, 37807056478, 0] := by
  rw [show A10K2.u3503 = KTree.node A10K2.u3501 (nat_lit 58017864) (nat_lit 12619673697) (nat_lit 0) A10K2.u3502 from rfl, totK_node, atot3501, atot3502]
  decide +kernel

theorem arows3507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3507 = true := by
  rw [show A10K2.u3507 = KTree.node A10K2.u3505 (nat_lit 58067020) (nat_lit 10942262896) (nat_lit 0) A10K2.u3506 from rfl, allE_node, arows3505, irow3507, arows3506]
  all_goals rfl

theorem atot3507 : totK PA10K2 A10K2.u3507 = [0, 0, 0, 1307392003468, 5718556458722, 8113512303795, 3626463237561, 463918239021, 12423235244, 0] := by
  rw [show A10K2.u3507 = KTree.node A10K2.u3505 (nat_lit 58067020) (nat_lit 10942262896) (nat_lit 0) A10K2.u3506 from rfl, totK_node, atot3505, atot3506]
  decide +kernel

theorem arows3510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3510 = true := by
  rw [show A10K2.u3510 = KTree.node A10K2.u3508 (nat_lit 58080670) (nat_lit 15386488801) (nat_lit 0) A10K2.u3509 from rfl, allE_node, arows3508, irow3510, arows3509]
  all_goals rfl

theorem atot3510 : totK PA10K2 A10K2.u3510 = [0, 0, 0, 1153302020972, 5436805103606, 7921703527312, 3709429067705, 555105693975, 31003444686, 0] := by
  rw [show A10K2.u3510 = KTree.node A10K2.u3508 (nat_lit 58080670) (nat_lit 15386488801) (nat_lit 0) A10K2.u3509 from rfl, totK_node, atot3508, atot3509]
  decide +kernel

theorem arows3517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3517 = true := by
  rw [show A10K2.u3517 = KTree.node A10K2.u3515 (nat_lit 58107575) (nat_lit 11911910263) (nat_lit 0) A10K2.u3516 from rfl, allE_node, arows3515, irow3517, arows3516]
  all_goals rfl

theorem atot3517 : totK PA10K2 A10K2.u3517 = [0, 0, 0, 0, 2541342390103, 8017290858703, 6529119095911, 1357692095807, 75274024722, 0] := by
  rw [show A10K2.u3517 = KTree.node A10K2.u3515 (nat_lit 58107575) (nat_lit 11911910263) (nat_lit 0) A10K2.u3516 from rfl, totK_node, atot3515, atot3516]
  decide +kernel

theorem arows3520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3520 = true := by
  rw [show A10K2.u3520 = KTree.node A10K2.u3518 (nat_lit 58199195) (nat_lit 8782014473) (nat_lit 0) A10K2.u3519 from rfl, allE_node, arows3518, irow3520, arows3519]
  all_goals rfl

theorem atot3520 : totK PA10K2 A10K2.u3520 = [0, 0, 1385427948510, 5091164601114, 5684709880708, 3160903680993, 2904118223949, 1386641425290, 196686909756, 6354482628] := by
  rw [show A10K2.u3520 = KTree.node A10K2.u3518 (nat_lit 58199195) (nat_lit 8782014473) (nat_lit 0) A10K2.u3519 from rfl, totK_node, atot3518, atot3519]
  decide +kernel

theorem arows3524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3524 = true := by
  rw [show A10K2.u3524 = KTree.node A10K2.u3522 (nat_lit 58271511) (nat_lit 10232697517) (nat_lit 0) A10K2.u3523 from rfl, allE_node, arows3522, irow3524, arows3523]
  all_goals rfl

theorem atot3524 : totK PA10K2 A10K2.u3524 = [0, 0, 845029706462, 4338634089158, 7728205695606, 5554387749654, 1404682394267, 88443054636, 0, 0] := by
  rw [show A10K2.u3524 = KTree.node A10K2.u3522 (nat_lit 58271511) (nat_lit 10232697517) (nat_lit 0) A10K2.u3523 from rfl, totK_node, atot3522, atot3523]
  decide +kernel

theorem arows3527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3527 = true := by
  rw [show A10K2.u3527 = KTree.node A10K2.u3525 (nat_lit 58283474) (nat_lit 15324262099) (nat_lit 0) A10K2.u3526 from rfl, allE_node, arows3525, irow3527, arows3526]
  all_goals rfl

theorem atot3527 : totK PA10K2 A10K2.u3527 = [0, 0, 1369984513015, 5828195262000, 8053902563821, 3759580410778, 470411306613, 12016267967, 0, 0] := by
  rw [show A10K2.u3527 = KTree.node A10K2.u3525 (nat_lit 58283474) (nat_lit 15324262099) (nat_lit 0) A10K2.u3526 from rfl, totK_node, atot3525, atot3526]
  decide +kernel

theorem arows3532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3532 = true := by
  rw [show A10K2.u3532 = KTree.node A10K2.u3530 (nat_lit 58303945) (nat_lit 2749237856) (nat_lit 0) A10K2.u3531 from rfl, allE_node, arows3530, irow3532, arows3531]
  all_goals rfl

theorem atot3532 : totK PA10K2 A10K2.u3532 = [0, 0, 0, 1777428534914, 6688343074865, 7853269683371, 3026101535376, 435807350811, 25565504801, 0] := by
  rw [show A10K2.u3532 = KTree.node A10K2.u3530 (nat_lit 58303945) (nat_lit 2749237856) (nat_lit 0) A10K2.u3531 from rfl, totK_node, atot3530, atot3531]
  decide +kernel

theorem arows3535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3535 = true := by
  rw [show A10K2.u3535 = KTree.node A10K2.u3533 (nat_lit 58319392) (nat_lit 7074180126) (nat_lit 128) A10K2.u3534 from rfl, allE_node, arows3533, irow3535, arows3534]
  all_goals rfl

theorem atot3535 : totK PA10K2 A10K2.u3535 = [0, 0, 424471676933, 2716747164552, 6690225750642, 6883844763653, 2672746019984, 310823706553, 5517381808, 0] := by
  rw [show A10K2.u3535 = KTree.node A10K2.u3533 (nat_lit 58319392) (nat_lit 7074180126) (nat_lit 128) A10K2.u3534 from rfl, totK_node, atot3533, atot3534]
  decide +kernel

theorem arows3539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3539 = true := by
  rw [show A10K2.u3539 = KTree.node A10K2.u3537 (nat_lit 58402976) (nat_lit 3807040598) (nat_lit 0) A10K2.u3538 from rfl, allE_node, arows3537, irow3539, arows3538]
  all_goals rfl

theorem atot3539 : totK PA10K2 A10K2.u3539 = [0, 0, 985500738873, 5054142231210, 8378077022246, 4803334829954, 783790546391, 33557803877, 0, 0] := by
  rw [show A10K2.u3539 = KTree.node A10K2.u3537 (nat_lit 58402976) (nat_lit 3807040598) (nat_lit 0) A10K2.u3538 from rfl, totK_node, atot3537, atot3538]
  decide +kernel

theorem arows3542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3542 = true := by
  rw [show A10K2.u3542 = KTree.node A10K2.u3540 (nat_lit 58421260) (nat_lit 10388109835) (nat_lit 0) A10K2.u3541 from rfl, allE_node, arows3540, irow3542, arows3541]
  all_goals rfl

theorem atot3542 : totK PA10K2 A10K2.u3542 = [0, 0, 873795323667, 4617142836063, 8107305406731, 5338068418035, 1150054395405, 62996513375, 0, 0] := by
  rw [show A10K2.u3542 = KTree.node A10K2.u3540 (nat_lit 58421260) (nat_lit 10388109835) (nat_lit 0) A10K2.u3541 from rfl, totK_node, atot3540, atot3541]
  decide +kernel

theorem arows3548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3548 = true := by
  rw [show A10K2.u3548 = KTree.node A10K2.u3546 (nat_lit 58437363) (nat_lit 9156035615) (nat_lit 0) A10K2.u3547 from rfl, allE_node, arows3546, irow3548, arows3547]
  all_goals rfl

theorem atot3548 : totK PA10K2 A10K2.u3548 = [0, 0, 0, 1519446652756, 6308146315996, 8135830265479, 3595358461873, 413933669504, 7047025452, 0] := by
  rw [show A10K2.u3548 = KTree.node A10K2.u3546 (nat_lit 58437363) (nat_lit 9156035615) (nat_lit 0) A10K2.u3547 from rfl, totK_node, atot3546, atot3547]
  decide +kernel

theorem arows3551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3551 = true := by
  rw [show A10K2.u3551 = KTree.node A10K2.u3549 (nat_lit 58457993) (nat_lit 6983035029) (nat_lit 32) A10K2.u3550 from rfl, allE_node, arows3549, irow3551, arows3550]
  all_goals rfl

theorem atot3551 : totK PA10K2 A10K2.u3551 = [0, 840727299041, 3245615607153, 4055400802133, 3459007265166, 4447066886972, 3024221344306, 696848734632, 41921244464, 0] := by
  rw [show A10K2.u3551 = KTree.node A10K2.u3549 (nat_lit 58457993) (nat_lit 6983035029) (nat_lit 32) A10K2.u3550 from rfl, totK_node, atot3549, atot3550]
  decide +kernel

theorem arows3555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3555 = true := by
  rw [show A10K2.u3555 = KTree.node A10K2.u3553 (nat_lit 58738024) (nat_lit 9145577888) (nat_lit 0) A10K2.u3554 from rfl, allE_node, arows3553, irow3555, arows3554]
  all_goals rfl

theorem atot3555 : totK PA10K2 A10K2.u3555 = [0, 948599761647, 4593177128235, 7744300180812, 4693715591562, 854305009199, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u3555 = KTree.node A10K2.u3553 (nat_lit 58738024) (nat_lit 9145577888) (nat_lit 0) A10K2.u3554 from rfl, totK_node, atot3553, atot3554]
  decide +kernel

theorem arows3558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3558 = true := by
  rw [show A10K2.u3558 = KTree.node A10K2.u3556 (nat_lit 58752918) (nat_lit 15989820252) (nat_lit 0) A10K2.u3557 from rfl, allE_node, arows3556, irow3558, arows3557]
  all_goals rfl

theorem atot3558 : totK PA10K2 A10K2.u3558 = [0, 390980993817, 3105533114043, 7600954450852, 6821093865672, 1885943530320, 122752375578, 0, 0, 0] := by
  rw [show A10K2.u3558 = KTree.node A10K2.u3556 (nat_lit 58752918) (nat_lit 15989820252) (nat_lit 0) A10K2.u3557 from rfl, totK_node, atot3556, atot3557]
  decide +kernel

theorem arows3563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3563 = true := by
  rw [show A10K2.u3563 = KTree.node A10K2.u3561 (nat_lit 58771283) (nat_lit 9112093830) (nat_lit 0) A10K2.u3562 from rfl, allE_node, arows3561, irow3563, arows3562]
  all_goals rfl

theorem atot3563 : totK PA10K2 A10K2.u3563 = [0, 0, 1039210890484, 4945232733201, 7780383838802, 4202548181628, 745600958495, 36196801203, 0, 0] := by
  rw [show A10K2.u3563 = KTree.node A10K2.u3561 (nat_lit 58771283) (nat_lit 9112093830) (nat_lit 0) A10K2.u3562 from rfl, totK_node, atot3561, atot3562]
  decide +kernel

theorem arows3566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3566 = true := by
  rw [show A10K2.u3566 = KTree.node A10K2.u3564 (nat_lit 58854897) (nat_lit 8621216862) (nat_lit 0) A10K2.u3565 from rfl, allE_node, arows3564, irow3566, arows3565]
  all_goals rfl

theorem atot3566 : totK PA10K2 A10K2.u3566 = [0, 1046080136887, 4792022748431, 7685472788754, 4966025201168, 1089507702217, 61661003203, 0, 0, 0] := by
  rw [show A10K2.u3566 = KTree.node A10K2.u3564 (nat_lit 58854897) (nat_lit 8621216862) (nat_lit 0) A10K2.u3565 from rfl, totK_node, atot3564, atot3565]
  decide +kernel

theorem arows3570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3570 = true := by
  rw [show A10K2.u3570 = KTree.node A10K2.u3568 (nat_lit 58868225) (nat_lit 10542815150) (nat_lit 0) A10K2.u3569 from rfl, allE_node, arows3568, irow3570, arows3569]
  all_goals rfl

theorem atot3570 : totK PA10K2 A10K2.u3570 = [0, 1101614959195, 5242384684978, 7962041910494, 4076620715217, 604735832539, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3570 = KTree.node A10K2.u3568 (nat_lit 58868225) (nat_lit 10542815150) (nat_lit 0) A10K2.u3569 from rfl, totK_node, atot3568, atot3569]
  decide +kernel

theorem arows3573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3573 = true := by
  rw [show A10K2.u3573 = KTree.node A10K2.u3571 (nat_lit 58893475) (nat_lit 10628298838) (nat_lit 0) A10K2.u3572 from rfl, allE_node, arows3571, irow3573, arows3572]
  all_goals rfl

theorem atot3573 : totK PA10K2 A10K2.u3573 = [0, 0, 2042484843356, 7430658777943, 7569377189343, 1947736744897, 116560142937, 0, 0, 0] := by
  rw [show A10K2.u3573 = KTree.node A10K2.u3571 (nat_lit 58893475) (nat_lit 10628298838) (nat_lit 0) A10K2.u3572 from rfl, totK_node, atot3571, atot3572]
  decide +kernel

theorem arows3583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3583 = true := by
  rw [show A10K2.u3583 = KTree.node A10K2.u3581 (nat_lit 58982797) (nat_lit 5029998014) (nat_lit 0) A10K2.u3582 from rfl, allE_node, arows3581, irow3583, arows3582]
  all_goals rfl

theorem atot3583 : totK PA10K2 A10K2.u3583 = [0, 0, 1140214467153, 5401150311527, 7976615628643, 3775231880744, 599048533365, 26425245443, 0, 0] := by
  rw [show A10K2.u3583 = KTree.node A10K2.u3581 (nat_lit 58982797) (nat_lit 5029998014) (nat_lit 0) A10K2.u3582 from rfl, totK_node, atot3581, atot3582]
  decide +kernel

theorem arows3586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3586 = true := by
  rw [show A10K2.u3586 = KTree.node A10K2.u3584 (nat_lit 59001110) (nat_lit 5302600857) (nat_lit 0) A10K2.u3585 from rfl, allE_node, arows3584, irow3586, arows3585]
  all_goals rfl

theorem atot3586 : totK PA10K2 A10K2.u3586 = [0, 0, 1148094586139, 5285745072849, 7978083397823, 3925671049779, 539094656211, 16465930986, 0, 0] := by
  rw [show A10K2.u3586 = KTree.node A10K2.u3584 (nat_lit 59001110) (nat_lit 5302600857) (nat_lit 0) A10K2.u3585 from rfl, totK_node, atot3584, atot3585]
  decide +kernel

theorem arows3590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3590 = true := by
  rw [show A10K2.u3590 = KTree.node A10K2.u3588 (nat_lit 59115585) (nat_lit 10335345372) (nat_lit 0) A10K2.u3589 from rfl, allE_node, arows3588, irow3590, arows3589]
  all_goals rfl

theorem atot3590 : totK PA10K2 A10K2.u3590 = [0, 0, 956757083827, 4897176477056, 8181904764308, 4724641447495, 788051226856, 37685021894, 0, 0] := by
  rw [show A10K2.u3590 = KTree.node A10K2.u3588 (nat_lit 59115585) (nat_lit 10335345372) (nat_lit 0) A10K2.u3589 from rfl, totK_node, atot3588, atot3589]
  decide +kernel

theorem arows3593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3593 = true := by
  rw [show A10K2.u3593 = KTree.node A10K2.u3591 (nat_lit 59129856) (nat_lit 15638348816) (nat_lit 0) A10K2.u3592 from rfl, allE_node, arows3591, irow3593, arows3592]
  all_goals rfl

theorem atot3593 : totK PA10K2 A10K2.u3593 = [0, 0, 1379681106734, 6003143476281, 8065498007775, 3247012053058, 332912363392, 6034215561, 0, 0] := by
  rw [show A10K2.u3593 = KTree.node A10K2.u3591 (nat_lit 59129856) (nat_lit 15638348816) (nat_lit 0) A10K2.u3592 from rfl, totK_node, atot3591, atot3592]
  decide +kernel

theorem arows3598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3598 = true := by
  rw [show A10K2.u3598 = KTree.node A10K2.u3596 (nat_lit 59149430) (nat_lit 16029065520) (nat_lit 0) A10K2.u3597 from rfl, allE_node, arows3596, irow3598, arows3597]
  all_goals rfl

theorem atot3598 : totK PA10K2 A10K2.u3598 = [0, 0, 0, 2445820565985, 7988016350648, 6760064452855, 1412336477646, 74987995932, 0, 0] := by
  rw [show A10K2.u3598 = KTree.node A10K2.u3596 (nat_lit 59149430) (nat_lit 16029065520) (nat_lit 0) A10K2.u3597 from rfl, totK_node, atot3596, atot3597]
  decide +kernel

theorem arows3601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3601 = true := by
  rw [show A10K2.u3601 = KTree.node A10K2.u3599 (nat_lit 59320324) (nat_lit 12088245603) (nat_lit 0) A10K2.u3600 from rfl, allE_node, arows3599, irow3601, arows3600]
  all_goals rfl

theorem atot3601 : totK PA10K2 A10K2.u3601 = [0, 860205094993, 3736700297015, 5380450698696, 4150537932502, 3305214390795, 1411054394821, 192289909650, 5676195732, 0] := by
  rw [show A10K2.u3601 = KTree.node A10K2.u3599 (nat_lit 59320324) (nat_lit 12088245603) (nat_lit 0) A10K2.u3600 from rfl, totK_node, atot3599, atot3600]
  decide +kernel

theorem arows3605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3605 = true := by
  rw [show A10K2.u3605 = KTree.node A10K2.u3603 (nat_lit 59329315) (nat_lit 9851281029) (nat_lit 0) A10K2.u3604 from rfl, allE_node, arows3603, irow3605, arows3604]
  all_goals rfl

theorem atot3605 : totK PA10K2 A10K2.u3605 = [0, 1320396235088, 5602069208394, 7870601078248, 3962350927613, 560852343266, 12388698189, 0, 0, 0] := by
  rw [show A10K2.u3605 = KTree.node A10K2.u3603 (nat_lit 59329315) (nat_lit 9851281029) (nat_lit 0) A10K2.u3604 from rfl, totK_node, atot3603, atot3604]
  decide +kernel

theorem arows3608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3608 = true := by
  rw [show A10K2.u3608 = KTree.node A10K2.u3606 (nat_lit 59352404) (nat_lit 12761557210) (nat_lit 0) A10K2.u3607 from rfl, allE_node, arows3606, irow3608, arows3607]
  all_goals rfl

theorem atot3608 : totK PA10K2 A10K2.u3608 = [0, 117664770764, 2225188637656, 7099976743200, 7555992367091, 2644635088277, 329592255779, 20331139758, 0, 0] := by
  rw [show A10K2.u3608 = KTree.node A10K2.u3606 (nat_lit 59352404) (nat_lit 12761557210) (nat_lit 0) A10K2.u3607 from rfl, totK_node, atot3606, atot3607]
  decide +kernel

theorem arows3614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3614 = true := by
  rw [show A10K2.u3614 = KTree.node A10K2.u3612 (nat_lit 59361500) (nat_lit 11285371633) (nat_lit 0) A10K2.u3613 from rfl, allE_node, arows3612, irow3614, arows3613]
  all_goals rfl

theorem atot3614 : totK PA10K2 A10K2.u3614 = [0, 0, 1141482795056, 5263002716213, 7914267074281, 4024760435809, 594829023283, 16872920140, 0, 0] := by
  rw [show A10K2.u3614 = KTree.node A10K2.u3612 (nat_lit 59361500) (nat_lit 11285371633) (nat_lit 0) A10K2.u3613 from rfl, totK_node, atot3612, atot3613]
  decide +kernel

theorem arows3617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3617 = true := by
  rw [show A10K2.u3617 = KTree.node A10K2.u3615 (nat_lit 59380036) (nat_lit 12314759380) (nat_lit 0) A10K2.u3616 from rfl, allE_node, arows3615, irow3617, arows3616]
  all_goals rfl

theorem atot3617 : totK PA10K2 A10K2.u3617 = [0, 1157305605063, 4897059077396, 7266842660237, 4547093255633, 1175080648975, 78915191039, 0, 0, 0] := by
  rw [show A10K2.u3617 = KTree.node A10K2.u3615 (nat_lit 59380036) (nat_lit 12314759380) (nat_lit 0) A10K2.u3616 from rfl, totK_node, atot3615, atot3616]
  decide +kernel

theorem arows3621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3621 = true := by
  rw [show A10K2.u3621 = KTree.node A10K2.u3619 (nat_lit 59392448) (nat_lit 14627273231) (nat_lit 0) A10K2.u3620 from rfl, allE_node, arows3619, irow3621, arows3620]
  all_goals rfl

theorem atot3621 : totK PA10K2 A10K2.u3621 = [0, 946272820892, 4945068213989, 8039911018724, 4542311387916, 742388590241, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3621 = KTree.node A10K2.u3619 (nat_lit 59392448) (nat_lit 14627273231) (nat_lit 0) A10K2.u3620 from rfl, totK_node, atot3619, atot3620]
  decide +kernel

theorem arows3624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3624 = true := by
  rw [show A10K2.u3624 = KTree.node A10K2.u3622 (nat_lit 59418330) (nat_lit 13978935762) (nat_lit 0) A10K2.u3623 from rfl, allE_node, arows3622, irow3624, arows3623]
  all_goals rfl

theorem atot3624 : totK PA10K2 A10K2.u3624 = [0, 0, 2072464667136, 7438554317679, 7429037708639, 1893029333106, 102420466534, 0, 0, 0] := by
  rw [show A10K2.u3624 = KTree.node A10K2.u3622 (nat_lit 59418330) (nat_lit 13978935762) (nat_lit 0) A10K2.u3623 from rfl, totK_node, atot3622, atot3623]
  decide +kernel

theorem arows3629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3629 = true := by
  rw [show A10K2.u3629 = KTree.node A10K2.u3627 (nat_lit 59450724) (nat_lit 13288879598) (nat_lit 0) A10K2.u3628 from rfl, allE_node, arows3627, irow3629, arows3628]
  all_goals rfl

theorem atot3629 : totK PA10K2 A10K2.u3629 = [0, 811248297904, 3590116716625, 6429718995544, 5903083749984, 2295863975394, 308239328621, 6354482628, 0, 0] := by
  rw [show A10K2.u3629 = KTree.node A10K2.u3627 (nat_lit 59450724) (nat_lit 13288879598) (nat_lit 0) A10K2.u3628 from rfl, totK_node, atot3627, atot3628]
  decide +kernel

theorem arows3632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3632 = true := by
  rw [show A10K2.u3632 = KTree.node A10K2.u3630 (nat_lit 59469326) (nat_lit 14635108191) (nat_lit 0) A10K2.u3631 from rfl, allE_node, arows3630, irow3632, arows3631]
  all_goals rfl

theorem atot3632 : totK PA10K2 A10K2.u3632 = [0, 798450316783, 4462734460506, 8367633998917, 5707744339001, 1155310624228, 48906959433, 0, 0, 0] := by
  rw [show A10K2.u3632 = KTree.node A10K2.u3630 (nat_lit 59469326) (nat_lit 14635108191) (nat_lit 0) A10K2.u3631 from rfl, totK_node, atot3630, atot3631]
  decide +kernel

theorem arows3636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3636 = true := by
  rw [show A10K2.u3636 = KTree.node A10K2.u3634 (nat_lit 59488512) (nat_lit 9116716672) (nat_lit 0) A10K2.u3635 from rfl, allE_node, arows3634, irow3636, arows3635]
  all_goals rfl

theorem atot3636 : totK PA10K2 A10K2.u3636 = [0, 0, 1381096804736, 6156953026387, 8519803705721, 3823057975813, 420777280070, 7047025452, 0, 0] := by
  rw [show A10K2.u3636 = KTree.node A10K2.u3634 (nat_lit 59488512) (nat_lit 9116716672) (nat_lit 0) A10K2.u3635 from rfl, totK_node, atot3634, atot3635]
  decide +kernel

theorem arows3639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3639 = true := by
  rw [show A10K2.u3639 = KTree.node A10K2.u3637 (nat_lit 59582314) (nat_lit 9751458855) (nat_lit 0) A10K2.u3638 from rfl, allE_node, arows3637, irow3639, arows3638]
  all_goals rfl

theorem atot3639 : totK PA10K2 A10K2.u3639 = [0, 0, 857710904603, 4432077804128, 7862178979407, 5377496770766, 1206379090458, 67655777756, 0, 0] := by
  rw [show A10K2.u3639 = KTree.node A10K2.u3637 (nat_lit 59582314) (nat_lit 9751458855) (nat_lit 0) A10K2.u3638 from rfl, totK_node, atot3637, atot3638]
  decide +kernel

theorem arows3646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3646 = true := by
  rw [show A10K2.u3646 = KTree.node A10K2.u3644 (nat_lit 59591456) (nat_lit 12401337551) (nat_lit 0) A10K2.u3645 from rfl, allE_node, arows3644, irow3646, arows3645]
  all_goals rfl

theorem atot3646 : totK PA10K2 A10K2.u3646 = [0, 0, 1318809125126, 5659102817084, 7961162757405, 3784904850524, 482155294290, 12273889295, 0, 0] := by
  rw [show A10K2.u3646 = KTree.node A10K2.u3644 (nat_lit 59591456) (nat_lit 12401337551) (nat_lit 0) A10K2.u3645 from rfl, totK_node, atot3644, atot3645]
  decide +kernel

theorem arows3649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3649 = true := by
  rw [show A10K2.u3649 = KTree.node A10K2.u3647 (nat_lit 59614654) (nat_lit 16085329573) (nat_lit 0) A10K2.u3648 from rfl, allE_node, arows3647, irow3649, arows3648]
  all_goals rfl

theorem atot3649 : totK PA10K2 A10K2.u3649 = [0, 0, 117664770764, 2195408583840, 6980199414405, 7336265349084, 2698284991866, 424454135214, 25565504801, 0] := by
  rw [show A10K2.u3649 = KTree.node A10K2.u3647 (nat_lit 59614654) (nat_lit 16085329573) (nat_lit 0) A10K2.u3648 from rfl, totK_node, atot3647, atot3648]
  decide +kernel

theorem arows3653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3653 = true := by
  rw [show A10K2.u3653 = KTree.node A10K2.u3651 (nat_lit 59623969) (nat_lit 9365372962) (nat_lit 0) A10K2.u3652 from rfl, allE_node, arows3651, irow3653, arows3652]
  all_goals rfl

theorem atot3653 : totK PA10K2 A10K2.u3653 = [0, 0, 0, 1367530940947, 5817967363998, 7791619995675, 3399127832089, 451721163676, 11138589073, 0] := by
  rw [show A10K2.u3653 = KTree.node A10K2.u3651 (nat_lit 59623969) (nat_lit 9365372962) (nat_lit 0) A10K2.u3652 from rfl, totK_node, atot3651, atot3652]
  decide +kernel

theorem arows3656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3656 = true := by
  rw [show A10K2.u3656 = KTree.node A10K2.u3654 (nat_lit 59644452) (nat_lit 13357059197) (nat_lit 0) A10K2.u3655 from rfl, allE_node, arows3654, irow3656, arows3655]
  all_goals rfl

theorem atot3656 : totK PA10K2 A10K2.u3656 = [0, 0, 1306223671615, 5608168155992, 7845329730912, 3782123680950, 650410799307, 35636906915, 0, 0] := by
  rw [show A10K2.u3656 = KTree.node A10K2.u3654 (nat_lit 59644452) (nat_lit 13357059197) (nat_lit 0) A10K2.u3655 from rfl, totK_node, atot3654, atot3655]
  decide +kernel

theorem arows3661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3661 = true := by
  rw [show A10K2.u3661 = KTree.node A10K2.u3659 (nat_lit 59655912) (nat_lit 4610272446) (nat_lit 0) A10K2.u3660 from rfl, allE_node, arows3659, irow3661, arows3660]
  all_goals rfl

theorem atot3661 : totK PA10K2 A10K2.u3661 = [0, 0, 810058863673, 4386423131537, 7800085911891, 4856565085090, 885119868972, 38123231481, 0, 0] := by
  rw [show A10K2.u3661 = KTree.node A10K2.u3659 (nat_lit 59655912) (nat_lit 4610272446) (nat_lit 0) A10K2.u3660 from rfl, totK_node, atot3659, atot3660]
  decide +kernel

theorem arows3664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3664 = true := by
  rw [show A10K2.u3664 = KTree.node A10K2.u3662 (nat_lit 59681979) (nat_lit 7143085881) (nat_lit 0) A10K2.u3663 from rfl, allE_node, arows3662, irow3664, arows3663]
  all_goals rfl

theorem atot3664 : totK PA10K2 A10K2.u3664 = [0, 0, 0, 1961643774007, 7410801205176, 7539510494066, 1787965291080, 93446806839, 0, 0] := by
  rw [show A10K2.u3664 = KTree.node A10K2.u3662 (nat_lit 59681979) (nat_lit 7143085881) (nat_lit 0) A10K2.u3663 from rfl, totK_node, atot3662, atot3663]
  decide +kernel

theorem arows3668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3668 = true := by
  rw [show A10K2.u3668 = KTree.node A10K2.u3666 (nat_lit 59714738) (nat_lit 15078393574) (nat_lit 0) A10K2.u3667 from rfl, allE_node, arows3666, irow3668, arows3667]
  all_goals rfl

theorem atot3668 : totK PA10K2 A10K2.u3668 = [0, 0, 1000610891292, 4287648222744, 6860540475211, 5390182148181, 1862061311658, 234179642854, 6239673734, 0] := by
  rw [show A10K2.u3668 = KTree.node A10K2.u3666 (nat_lit 59714738) (nat_lit 15078393574) (nat_lit 0) A10K2.u3667 from rfl, totK_node, atot3666, atot3667]
  decide +kernel

theorem arows3671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3671 = true := by
  rw [show A10K2.u3671 = KTree.node A10K2.u3669 (nat_lit 59733497) (nat_lit 6028598448) (nat_lit 0) A10K2.u3670 from rfl, allE_node, arows3669, irow3671, arows3670]
  all_goals rfl

theorem atot3671 : totK PA10K2 A10K2.u3671 = [0, 573258531646, 2690937306788, 5371058717800, 6457379502427, 4085414047146, 887959652556, 42874818239, 0, 0] := by
  rw [show A10K2.u3671 = KTree.node A10K2.u3669 (nat_lit 59733497) (nat_lit 6028598448) (nat_lit 0) A10K2.u3670 from rfl, totK_node, atot3669, atot3670]
  decide +kernel

theorem arows3677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3677 = true := by
  rw [show A10K2.u3677 = KTree.node A10K2.u3675 (nat_lit 59785671) (nat_lit 13253028956) (nat_lit 0) A10K2.u3676 from rfl, allE_node, arows3675, irow3677, arows3676]
  all_goals rfl

theorem atot3677 : totK PA10K2 A10K2.u3677 = [0, 967696959595, 4945783829088, 8078075845239, 4455637413301, 721267679293, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3677 = KTree.node A10K2.u3675 (nat_lit 59785671) (nat_lit 13253028956) (nat_lit 0) A10K2.u3676 from rfl, totK_node, atot3675, atot3676]
  decide +kernel

theorem arows3680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3680 = true := by
  rw [show A10K2.u3680 = KTree.node A10K2.u3678 (nat_lit 59802545) (nat_lit 9107130710) (nat_lit 0) A10K2.u3679 from rfl, allE_node, arows3678, irow3680, arows3679]
  all_goals rfl

theorem atot3680 : totK PA10K2 A10K2.u3680 = [0, 266424507814, 2105241031695, 6061133144060, 7043568698206, 2976736891091, 482685947176, 30650496230, 0, 0] := by
  rw [show A10K2.u3680 = KTree.node A10K2.u3678 (nat_lit 59802545) (nat_lit 9107130710) (nat_lit 0) A10K2.u3679 from rfl, totK_node, atot3678, atot3679]
  decide +kernel

theorem arows3684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3684 = true := by
  rw [show A10K2.u3684 = KTree.node A10K2.u3682 (nat_lit 59823404) (nat_lit 13378416925) (nat_lit 0) A10K2.u3683 from rfl, allE_node, arows3682, irow3684, arows3683]
  all_goals rfl

theorem atot3684 : totK PA10K2 A10K2.u3684 = [0, 582775338075, 2900960784594, 6304789976003, 6615635480572, 2404333087318, 258465677313, 5546304973, 0, 0] := by
  rw [show A10K2.u3684 = KTree.node A10K2.u3682 (nat_lit 59823404) (nat_lit 13378416925) (nat_lit 0) A10K2.u3683 from rfl, totK_node, atot3682, atot3683]
  decide +kernel

theorem arows3687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3687 = true := by
  rw [show A10K2.u3687 = KTree.node A10K2.u3685 (nat_lit 59850133) (nat_lit 4503444168) (nat_lit 0) A10K2.u3686 from rfl, allE_node, arows3685, irow3687, arows3686]
  all_goals rfl

theorem atot3687 : totK PA10K2 A10K2.u3687 = [0, 1014760276576, 5078258699177, 8060930748041, 4392271705765, 722667123287, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3687 = KTree.node A10K2.u3685 (nat_lit 59850133) (nat_lit 4503444168) (nat_lit 0) A10K2.u3686 from rfl, totK_node, atot3685, atot3686]
  decide +kernel

theorem arows3692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3692 = true := by
  rw [show A10K2.u3692 = KTree.node A10K2.u3690 (nat_lit 59864469) (nat_lit 4984278585) (nat_lit 0) A10K2.u3691 from rfl, allE_node, arows3690, irow3692, arows3691]
  all_goals rfl

theorem atot3692 : totK PA10K2 A10K2.u3692 = [0, 502723522018, 3539889096973, 7945251380901, 6284084430998, 1473944902764, 81689804167, 0, 0, 0] := by
  rw [show A10K2.u3692 = KTree.node A10K2.u3690 (nat_lit 59864469) (nat_lit 4984278585) (nat_lit 0) A10K2.u3691 from rfl, totK_node, atot3690, atot3691]
  decide +kernel

theorem arows3695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3695 = true := by
  rw [show A10K2.u3695 = KTree.node A10K2.u3693 (nat_lit 59884088) (nat_lit 13614323418) (nat_lit 0) A10K2.u3694 from rfl, allE_node, arows3693, irow3695, arows3694]
  all_goals rfl

theorem atot3695 : totK PA10K2 A10K2.u3695 = [0, 0, 878226349513, 4900121200531, 8188463612945, 4332537254403, 677019030299, 31082886609, 0, 0] := by
  rw [show A10K2.u3695 = KTree.node A10K2.u3693 (nat_lit 59884088) (nat_lit 13614323418) (nat_lit 0) A10K2.u3694 from rfl, totK_node, atot3693, atot3694]
  decide +kernel

theorem arows3699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3699 = true := by
  rw [show A10K2.u3699 = KTree.node A10K2.u3697 (nat_lit 59902020) (nat_lit 11665821275) (nat_lit 0) A10K2.u3698 from rfl, allE_node, arows3697, irow3699, arows3698]
  all_goals rfl

theorem atot3699 : totK PA10K2 A10K2.u3699 = [0, 696624018698, 3727965573857, 6911034451543, 5482453588452, 1895782201141, 235695050700, 6121173289, 0, 0] := by
  rw [show A10K2.u3699 = KTree.node A10K2.u3697 (nat_lit 59902020) (nat_lit 11665821275) (nat_lit 0) A10K2.u3698 from rfl, totK_node, atot3697, atot3698]
  decide +kernel

theorem arows3702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3702 = true := by
  rw [show A10K2.u3702 = KTree.node A10K2.u3700 (nat_lit 59913974) (nat_lit 13553652218) (nat_lit 0) A10K2.u3701 from rfl, allE_node, arows3700, irow3702, arows3701]
  all_goals rfl

theorem atot3702 : totK PA10K2 A10K2.u3702 = [0, 1288862271969, 5448999102732, 7697088295603, 4045613849079, 694857450407, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3702 = KTree.node A10K2.u3700 (nat_lit 59913974) (nat_lit 13553652218) (nat_lit 0) A10K2.u3701 from rfl, totK_node, atot3700, atot3701]
  decide +kernel

theorem arows3710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3710 = true := by
  rw [show A10K2.u3710 = KTree.node A10K2.u3708 (nat_lit 59933114) (nat_lit 17340992) (nat_lit 0) A10K2.u3709 from rfl, allE_node, arows3708, irow3710, arows3709]
  all_goals rfl

theorem atot3710 : totK PA10K2 A10K2.u3710 = [0, 295989007569, 3207518955560, 7772246702143, 6144996656351, 1362325062289, 71254002758, 0, 0, 0] := by
  rw [show A10K2.u3710 = KTree.node A10K2.u3708 (nat_lit 59933114) (nat_lit 17340992) (nat_lit 0) A10K2.u3709 from rfl, totK_node, atot3708, atot3709]
  decide +kernel

theorem arows3713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3713 = true := by
  rw [show A10K2.u3713 = KTree.node A10K2.u3711 (nat_lit 59951388) (nat_lit 12251271232) (nat_lit 0) A10K2.u3712 from rfl, allE_node, arows3711, irow3713, arows3712]
  all_goals rfl

theorem atot3713 : totK PA10K2 A10K2.u3713 = [0, 0, 1355518199181, 6067450579875, 8021086232212, 3019429103284, 354954660074, 6354482628, 0, 0] := by
  rw [show A10K2.u3713 = KTree.node A10K2.u3711 (nat_lit 59951388) (nat_lit 12251271232) (nat_lit 0) A10K2.u3712 from rfl, totK_node, atot3711, atot3712]
  decide +kernel

theorem arows3717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3717 = true := by
  rw [show A10K2.u3717 = KTree.node A10K2.u3715 (nat_lit 60038156) (nat_lit 10217015745) (nat_lit 0) A10K2.u3716 from rfl, allE_node, arows3715, irow3717, arows3716]
  all_goals rfl

theorem atot3717 : totK PA10K2 A10K2.u3717 = [0, 0, 1235709676364, 5508590909605, 7919635255907, 3805753553537, 556967177330, 30818366867, 0, 0] := by
  rw [show A10K2.u3717 = KTree.node A10K2.u3715 (nat_lit 60038156) (nat_lit 10217015745) (nat_lit 0) A10K2.u3716 from rfl, totK_node, atot3715, atot3716]
  decide +kernel

theorem arows3720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3720 = true := by
  rw [show A10K2.u3720 = KTree.node A10K2.u3718 (nat_lit 60106390) (nat_lit 14938990363) (nat_lit 0) A10K2.u3719 from rfl, allE_node, arows3718, irow3720, arows3719]
  all_goals rfl

theorem atot3720 : totK PA10K2 A10K2.u3720 = [0, 0, 1081526810407, 5126655965230, 7965038488781, 4269131065971, 716380460344, 32089015920, 0, 0] := by
  rw [show A10K2.u3720 = KTree.node A10K2.u3718 (nat_lit 60106390) (nat_lit 14938990363) (nat_lit 0) A10K2.u3719 from rfl, totK_node, atot3718, atot3719]
  decide +kernel

theorem arows3725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3725 = true := by
  rw [show A10K2.u3725 = KTree.node A10K2.u3723 (nat_lit 60115285) (nat_lit 6980450443) (nat_lit 0) A10K2.u3724 from rfl, allE_node, arows3723, irow3725, arows3724]
  all_goals rfl

theorem atot3725 : totK PA10K2 A10K2.u3725 = [0, 0, 1170566346776, 5336065011778, 8006782142256, 4089035044230, 555344313641, 12072523186, 0, 0] := by
  rw [show A10K2.u3725 = KTree.node A10K2.u3723 (nat_lit 60115285) (nat_lit 6980450443) (nat_lit 0) A10K2.u3724 from rfl, totK_node, atot3723, atot3724]
  decide +kernel

theorem arows3728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3728 = true := by
  rw [show A10K2.u3728 = KTree.node A10K2.u3726 (nat_lit 60164453) (nat_lit 7336690236) (nat_lit 0) A10K2.u3727 from rfl, allE_node, arows3726, irow3728, arows3727]
  all_goals rfl

theorem atot3728 : totK PA10K2 A10K2.u3728 = [0, 0, 1101944316051, 4895957020035, 7729856197313, 4422941212386, 771174134215, 37037625897, 0, 0] := by
  rw [show A10K2.u3728 = KTree.node A10K2.u3726 (nat_lit 60164453) (nat_lit 7336690236) (nat_lit 0) A10K2.u3727 from rfl, totK_node, atot3726, atot3727]
  decide +kernel

theorem arows3732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3732 = true := by
  rw [show A10K2.u3732 = KTree.node A10K2.u3730 (nat_lit 60176641) (nat_lit 9770762046) (nat_lit 0) A10K2.u3731 from rfl, allE_node, arows3730, irow3732, arows3731]
  all_goals rfl

theorem atot3732 : totK PA10K2 A10K2.u3732 = [0, 0, 1301340303726, 5612966828151, 7739208868063, 3717165923041, 572792299111, 31003444686, 0, 0] := by
  rw [show A10K2.u3732 = KTree.node A10K2.u3730 (nat_lit 60176641) (nat_lit 9770762046) (nat_lit 0) A10K2.u3731 from rfl, totK_node, atot3730, atot3731]
  decide +kernel

theorem arows3735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3735 = true := by
  rw [show A10K2.u3735 = KTree.node A10K2.u3733 (nat_lit 60196921) (nat_lit 7197847521) (nat_lit 0) A10K2.u3734 from rfl, allE_node, arows3733, irow3735, arows3734]
  all_goals rfl

theorem atot3735 : totK PA10K2 A10K2.u3735 = [0, 0, 0, 2646247701887, 8140500581258, 6370117092317, 1327576119129, 69238617717, 0, 0] := by
  rw [show A10K2.u3735 = KTree.node A10K2.u3733 (nat_lit 60196921) (nat_lit 7197847521) (nat_lit 0) A10K2.u3734 from rfl, totK_node, atot3733, atot3734]
  decide +kernel

theorem arows3741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3741 = true := by
  rw [show A10K2.u3741 = KTree.node A10K2.u3739 (nat_lit 60216640) (nat_lit 11527065867) (nat_lit 0) A10K2.u3740 from rfl, allE_node, arows3739, irow3741, arows3740]
  all_goals rfl

theorem atot3741 : totK PA10K2 A10K2.u3741 = [0, 0, 840727299041, 3479736343303, 6069216203800, 5621495783272, 2238975304441, 315723946146, 6354482628, 0] := by
  rw [show A10K2.u3741 = KTree.node A10K2.u3739 (nat_lit 60216640) (nat_lit 11527065867) (nat_lit 0) A10K2.u3740 from rfl, totK_node, atot3739, atot3740]
  decide +kernel

theorem arows3744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3744 = true := by
  rw [show A10K2.u3744 = KTree.node A10K2.u3742 (nat_lit 60834252) (nat_lit 7394287599) (nat_lit 0) A10K2.u3743 from rfl, allE_node, arows3742, irow3744, arows3743]
  all_goals rfl

theorem atot3744 : totK PA10K2 A10K2.u3744 = [0, 0, 744326850038, 4595066193087, 8318641733658, 4609062144359, 694718402494, 30831673886, 0, 0] := by
  rw [show A10K2.u3744 = KTree.node A10K2.u3742 (nat_lit 60834252) (nat_lit 7394287599) (nat_lit 0) A10K2.u3743 from rfl, totK_node, atot3742, atot3743]
  decide +kernel

theorem arows3748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3748 = true := by
  rw [show A10K2.u3748 = KTree.node A10K2.u3746 (nat_lit 60849252) (nat_lit 8688051196) (nat_lit 0) A10K2.u3747 from rfl, allE_node, arows3746, irow3748, arows3747]
  all_goals rfl

theorem atot3748 : totK PA10K2 A10K2.u3748 = [0, 0, 593403324104, 3682011728668, 7899607837887, 6371188262913, 1343513264914, 57118382332, 0, 0] := by
  rw [show A10K2.u3748 = KTree.node A10K2.u3746 (nat_lit 60849252) (nat_lit 8688051196) (nat_lit 0) A10K2.u3747 from rfl, totK_node, atot3746, atot3747]
  decide +kernel

theorem arows3751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3751 = true := by
  rw [show A10K2.u3751 = KTree.node A10K2.u3749 (nat_lit 60872936) (nat_lit 7217163367) (nat_lit 0) A10K2.u3750 from rfl, allE_node, arows3749, irow3751, arows3750]
  all_goals rfl

theorem atot3751 : totK PA10K2 A10K2.u3751 = [0, 0, 536209087732, 2876709484263, 6672556646166, 6622834299006, 2106941213413, 231720856177, 5546304973, 0] := by
  rw [show A10K2.u3751 = KTree.node A10K2.u3749 (nat_lit 60872936) (nat_lit 7217163367) (nat_lit 0) A10K2.u3750 from rfl, totK_node, atot3749, atot3750]
  decide +kernel

theorem arows3756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3756 = true := by
  rw [show A10K2.u3756 = KTree.node A10K2.u3754 (nat_lit 60957854) (nat_lit 14235350830) (nat_lit 0) A10K2.u3755 from rfl, allE_node, arows3754, irow3756, arows3755]
  all_goals rfl

theorem atot3756 : totK PA10K2 A10K2.u3756 = [0, 0, 790211852084, 4516565606608, 8120306684776, 4930025187361, 775935347304, 36225297058, 0, 0] := by
  rw [show A10K2.u3756 = KTree.node A10K2.u3754 (nat_lit 60957854) (nat_lit 14235350830) (nat_lit 0) A10K2.u3755 from rfl, totK_node, atot3754, atot3755]
  decide +kernel

theorem arows3759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3759 = true := by
  rw [show A10K2.u3759 = KTree.node A10K2.u3757 (nat_lit 60969406) (nat_lit 11640880091) (nat_lit 0) A10K2.u3758 from rfl, allE_node, arows3757, irow3759, arows3758]
  all_goals rfl

theorem atot3759 : totK PA10K2 A10K2.u3759 = [0, 0, 815829842394, 4395412491355, 7719028542165, 4922545803279, 917996892633, 44376575138, 0, 0] := by
  rw [show A10K2.u3759 = KTree.node A10K2.u3757 (nat_lit 60969406) (nat_lit 11640880091) (nat_lit 0) A10K2.u3758 from rfl, totK_node, atot3757, atot3758]
  decide +kernel

theorem arows3763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3763 = true := by
  rw [show A10K2.u3763 = KTree.node A10K2.u3761 (nat_lit 60998925) (nat_lit 5921011772) (nat_lit 0) A10K2.u3762 from rfl, allE_node, arows3761, irow3763, arows3762]
  all_goals rfl

theorem atot3763 : totK PA10K2 A10K2.u3763 = [0, 0, 118410781347, 1790217980741, 6557143301820, 7711351022937, 2451734449896, 257761165857, 6354482628, 0] := by
  rw [show A10K2.u3763 = KTree.node A10K2.u3761 (nat_lit 60998925) (nat_lit 5921011772) (nat_lit 0) A10K2.u3762 from rfl, totK_node, atot3761, atot3762]
  decide +kernel

theorem arows3766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3766 = true := by
  rw [show A10K2.u3766 = KTree.node A10K2.u3764 (nat_lit 61421207) (nat_lit 12851081873) (nat_lit 0) A10K2.u3765 from rfl, allE_node, arows3764, irow3766, arows3765]
  all_goals rfl

theorem atot3766 : totK PA10K2 A10K2.u3766 = [0, 0, 1199023466592, 5364354523958, 7879091909527, 4192098185964, 692416159103, 31768748853, 0, 0] := by
  rw [show A10K2.u3766 = KTree.node A10K2.u3764 (nat_lit 61421207) (nat_lit 12851081873) (nat_lit 0) A10K2.u3765 from rfl, totK_node, atot3764, atot3765]
  decide +kernel

theorem arows3773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3773 = true := by
  rw [show A10K2.u3773 = KTree.node A10K2.u3771 (nat_lit 61433239) (nat_lit 14384969889) (nat_lit 0) A10K2.u3772 from rfl, allE_node, arows3771, irow3773, arows3772]
  all_goals rfl

theorem atot3773 : totK PA10K2 A10K2.u3773 = [0, 0, 980831852906, 5065418553312, 8436367959760, 4755114269140, 650655949677, 13317224979, 0, 0] := by
  rw [show A10K2.u3773 = KTree.node A10K2.u3771 (nat_lit 61433239) (nat_lit 14384969889) (nat_lit 0) A10K2.u3772 from rfl, totK_node, atot3771, atot3772]
  decide +kernel

theorem arows3776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3776 = true := by
  rw [show A10K2.u3776 = KTree.node A10K2.u3774 (nat_lit 61453462) (nat_lit 14758452160) (nat_lit 0) A10K2.u3775 from rfl, allE_node, arows3774, irow3776, arows3775]
  all_goals rfl

theorem atot3776 : totK PA10K2 A10K2.u3776 = [0, 0, 0, 1313935069726, 5643570203875, 7829684200536, 3744320297268, 634069174565, 31082886609, 0] := by
  rw [show A10K2.u3776 = KTree.node A10K2.u3774 (nat_lit 61453462) (nat_lit 14758452160) (nat_lit 0) A10K2.u3775 from rfl, totK_node, atot3774, atot3775]
  decide +kernel

theorem arows3780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3780 = true := by
  rw [show A10K2.u3780 = KTree.node A10K2.u3778 (nat_lit 61465814) (nat_lit 15000960781) (nat_lit 0) A10K2.u3779 from rfl, allE_node, arows3778, irow3780, arows3779]
  all_goals rfl

theorem atot3780 : totK PA10K2 A10K2.u3780 = [0, 0, 516552094339, 2819702115819, 6224774130599, 6720645687792, 2659613305642, 284430994552, 6121173289, 0] := by
  rw [show A10K2.u3780 = KTree.node A10K2.u3778 (nat_lit 61465814) (nat_lit 15000960781) (nat_lit 0) A10K2.u3779 from rfl, totK_node, atot3778, atot3779]
  decide +kernel

theorem arows3783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3783 = true := by
  rw [show A10K2.u3783 = KTree.node A10K2.u3781 (nat_lit 61483683) (nat_lit 10480732544) (nat_lit 0) A10K2.u3782 from rfl, allE_node, arows3781, irow3783, arows3782]
  all_goals rfl

theorem atot3783 : totK PA10K2 A10K2.u3783 = [0, 0, 885033750842, 4401258845657, 7862591895821, 5106738522984, 943231432891, 42529659924, 0, 0] := by
  rw [show A10K2.u3783 = KTree.node A10K2.u3781 (nat_lit 61483683) (nat_lit 10480732544) (nat_lit 0) A10K2.u3782 from rfl, totK_node, atot3781, atot3782]
  decide +kernel

theorem arows3788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3788 = true := by
  rw [show A10K2.u3788 = KTree.node A10K2.u3786 (nat_lit 61494558) (nat_lit 10422054429) (nat_lit 0) A10K2.u3787 from rfl, allE_node, arows3786, irow3788, arows3787]
  all_goals rfl

theorem atot3788 : totK PA10K2 A10K2.u3788 = [0, 0, 714696690107, 4370804656336, 8075833595567, 4839757506853, 722972498032, 18095079033, 0, 0] := by
  rw [show A10K2.u3788 = KTree.node A10K2.u3786 (nat_lit 61494558) (nat_lit 10422054429) (nat_lit 0) A10K2.u3787 from rfl, totK_node, atot3786, atot3787]
  decide +kernel

theorem arows3791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3791 = true := by
  rw [show A10K2.u3791 = KTree.node A10K2.u3789 (nat_lit 61523613) (nat_lit 6085757737) (nat_lit 0) A10K2.u3790 from rfl, allE_node, arows3789, irow3791, arows3790]
  all_goals rfl

theorem atot3791 : totK PA10K2 A10K2.u3791 = [0, 0, 202041260899, 1700026759781, 5994953903426, 7772373356300, 2847687302142, 305534987938, 6354482628, 0] := by
  rw [show A10K2.u3791 = KTree.node A10K2.u3789 (nat_lit 61523613) (nat_lit 6085757737) (nat_lit 0) A10K2.u3790 from rfl, totK_node, atot3789, atot3790]
  decide +kernel

theorem arows3795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3795 = true := by
  rw [show A10K2.u3795 = KTree.node A10K2.u3793 (nat_lit 61552490) (nat_lit 9713072085) (nat_lit 0) A10K2.u3794 from rfl, allE_node, arows3793, irow3795, arows3794]
  all_goals rfl

theorem atot3795 : totK PA10K2 A10K2.u3795 = [0, 0, 1407657353788, 5990781661431, 8175838249557, 4041782191788, 664442536954, 31522233512, 0, 0] := by
  rw [show A10K2.u3795 = KTree.node A10K2.u3793 (nat_lit 61552490) (nat_lit 9713072085) (nat_lit 0) A10K2.u3794 from rfl, totK_node, atot3793, atot3794]
  decide +kernel

theorem arows3798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3798 = true := by
  rw [show A10K2.u3798 = KTree.node A10K2.u3796 (nat_lit 61580642) (nat_lit 13046092967) (nat_lit 0) A10K2.u3797 from rfl, allE_node, arows3796, irow3798, arows3797]
  all_goals rfl

theorem atot3798 : totK PA10K2 A10K2.u3798 = [0, 0, 0, 1915563009585, 7180032693049, 7966139361067, 2833313476749, 320656671723, 7047025452, 0] := by
  rw [show A10K2.u3798 = KTree.node A10K2.u3796 (nat_lit 61580642) (nat_lit 13046092967) (nat_lit 0) A10K2.u3797 from rfl, totK_node, atot3796, atot3797]
  decide +kernel

theorem arows3804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3804 = true := by
  rw [show A10K2.u3804 = KTree.node A10K2.u3802 (nat_lit 61866559) (nat_lit 10355336737) (nat_lit 0) A10K2.u3803 from rfl, allE_node, arows3802, irow3804, arows3803]
  all_goals rfl

theorem atot3804 : totK PA10K2 A10K2.u3804 = [0, 0, 761005751305, 4140416895650, 7690107693226, 5553785037454, 1495645320216, 109188516300, 0, 0] := by
  rw [show A10K2.u3804 = KTree.node A10K2.u3802 (nat_lit 61866559) (nat_lit 10355336737) (nat_lit 0) A10K2.u3803 from rfl, totK_node, atot3802, atot3803]
  decide +kernel

theorem arows3807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3807 = true := by
  rw [show A10K2.u3807 = KTree.node A10K2.u3805 (nat_lit 61886477) (nat_lit 5771049398) (nat_lit 0) A10K2.u3806 from rfl, allE_node, arows3805, irow3807, arows3806]
  all_goals rfl

theorem atot3807 : totK PA10K2 A10K2.u3807 = [0, 0, 1045008235948, 5117073672649, 8059885557143, 4317739135471, 582147865376, 11814975521, 0, 0] := by
  rw [show A10K2.u3807 = KTree.node A10K2.u3805 (nat_lit 61886477) (nat_lit 5771049398) (nat_lit 0) A10K2.u3806 from rfl, totK_node, atot3805, atot3806]
  decide +kernel

theorem arows3811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3811 = true := by
  rw [show A10K2.u3811 = KTree.node A10K2.u3809 (nat_lit 61916374) (nat_lit 12442486376) (nat_lit 0) A10K2.u3810 from rfl, allE_node, arows3809, irow3811, arows3810]
  all_goals rfl

theorem atot3811 : totK PA10K2 A10K2.u3811 = [0, 0, 0, 1662006929662, 6707422888155, 7788056982875, 2432873421864, 255140400575, 5546304973, 0] := by
  rw [show A10K2.u3811 = KTree.node A10K2.u3809 (nat_lit 61916374) (nat_lit 12442486376) (nat_lit 0) A10K2.u3810 from rfl, totK_node, atot3809, atot3810]
  decide +kernel

theorem arows3814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3814 = true := by
  rw [show A10K2.u3814 = KTree.node A10K2.u3812 (nat_lit 61945079) (nat_lit 13988559452) (nat_lit 0) A10K2.u3813 from rfl, allE_node, arows3812, irow3814, arows3813]
  all_goals rfl

theorem atot3814 : totK PA10K2 A10K2.u3814 = [0, 0, 1296775117300, 5307697378227, 7612232344609, 4334018764610, 732190714480, 31768748853, 0, 0] := by
  rw [show A10K2.u3814 = KTree.node A10K2.u3812 (nat_lit 61945079) (nat_lit 13988559452) (nat_lit 0) A10K2.u3813 from rfl, totK_node, atot3812, atot3813]
  decide +kernel

theorem arows3819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3819 = true := by
  rw [show A10K2.u3819 = KTree.node A10K2.u3817 (nat_lit 61957346) (nat_lit 14279361898) (nat_lit 0) A10K2.u3818 from rfl, allE_node, arows3817, irow3819, arows3818]
  all_goals rfl

theorem atot3819 : totK PA10K2 A10K2.u3819 = [0, 0, 800788206144, 4763238811397, 8512935355975, 4895020013930, 757655753246, 19280604132, 0, 0] := by
  rw [show A10K2.u3819 = KTree.node A10K2.u3817 (nat_lit 61957346) (nat_lit 14279361898) (nat_lit 0) A10K2.u3818 from rfl, totK_node, atot3817, atot3818]
  decide +kernel

theorem arows3822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3822 = true := by
  rw [show A10K2.u3822 = KTree.node A10K2.u3820 (nat_lit 61978806) (nat_lit 12797929781) (nat_lit 0) A10K2.u3821 from rfl, allE_node, arows3820, irow3822, arows3821]
  all_goals rfl

theorem atot3822 : totK PA10K2 A10K2.u3822 = [0, 0, 0, 1319454513452, 5941180892569, 7877889760904, 3314553291821, 516474732774, 30647824416, 0] := by
  rw [show A10K2.u3822 = KTree.node A10K2.u3820 (nat_lit 61978806) (nat_lit 12797929781) (nat_lit 0) A10K2.u3821 from rfl, totK_node, atot3820, atot3821]
  decide +kernel

theorem arows3826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3826 = true := by
  rw [show A10K2.u3826 = KTree.node A10K2.u3824 (nat_lit 61997088) (nat_lit 14351772385) (nat_lit 0) A10K2.u3825 from rfl, allE_node, arows3824, irow3826, arows3825]
  all_goals rfl

theorem atot3826 : totK PA10K2 A10K2.u3826 = [0, 0, 696624018698, 3310135713497, 6286030886925, 5983558061713, 2287327498933, 271523284134, 6121173289, 0] := by
  rw [show A10K2.u3826 = KTree.node A10K2.u3824 (nat_lit 61997088) (nat_lit 14351772385) (nat_lit 0) A10K2.u3825 from rfl, totK_node, atot3824, atot3825]
  decide +kernel

theorem arows3829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3829 = true := by
  rw [show A10K2.u3829 = KTree.node A10K2.u3827 (nat_lit 62008986) (nat_lit 15094184054) (nat_lit 0) A10K2.u3828 from rfl, allE_node, arows3827, irow3829, arows3828]
  all_goals rfl

theorem atot3829 : totK PA10K2 A10K2.u3829 = [0, 0, 1011946647917, 4791012376314, 7784519612268, 4603443296103, 778293261396, 37229241746, 0, 0] := by
  rw [show A10K2.u3829 = KTree.node A10K2.u3827 (nat_lit 62008986) (nat_lit 15094184054) (nat_lit 0) A10K2.u3828 from rfl, totK_node, atot3827, atot3828]
  decide +kernel

theorem arows3838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3838 = true := by
  rw [show A10K2.u3838 = KTree.node A10K2.u3836 (nat_lit 62019831) (nat_lit 5350882547) (nat_lit 0) A10K2.u3837 from rfl, allE_node, arows3836, irow3838, arows3837]
  all_goals rfl

theorem atot3838 : totK PA10K2 A10K2.u3838 = [0, 0, 582523478866, 3980753770992, 8035962066714, 5293295039140, 890857537821, 38342359577, 0, 0] := by
  rw [show A10K2.u3838 = KTree.node A10K2.u3836 (nat_lit 62019831) (nat_lit 5350882547) (nat_lit 0) A10K2.u3837 from rfl, totK_node, atot3836, atot3837]
  decide +kernel

theorem arows3841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3841 = true := by
  rw [show A10K2.u3841 = KTree.node A10K2.u3839 (nat_lit 62047742) (nat_lit 8029683694) (nat_lit 0) A10K2.u3840 from rfl, allE_node, arows3839, irow3841, arows3840]
  all_goals rfl

theorem atot3841 : totK PA10K2 A10K2.u3841 = [0, 0, 0, 1411466868020, 6104072680872, 7975275066221, 2943942222679, 354947535203, 6354482628, 0] := by
  rw [show A10K2.u3841 = KTree.node A10K2.u3839 (nat_lit 62047742) (nat_lit 8029683694) (nat_lit 0) A10K2.u3840 from rfl, totK_node, atot3839, atot3840]
  decide +kernel

theorem arows3845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3845 = true := by
  rw [show A10K2.u3845 = KTree.node A10K2.u3843 (nat_lit 62135052) (nat_lit 11808228873) (nat_lit 0) A10K2.u3844 from rfl, allE_node, arows3843, irow3845, arows3844]
  all_goals rfl

theorem atot3845 : totK PA10K2 A10K2.u3845 = [0, 0, 0, 1416063865298, 6306454505883, 8143066113508, 2808466485578, 289027004956, 5447185874, 0] := by
  rw [show A10K2.u3845 = KTree.node A10K2.u3843 (nat_lit 62135052) (nat_lit 11808228873) (nat_lit 0) A10K2.u3844 from rfl, totK_node, atot3843, atot3844]
  decide +kernel

theorem arows3848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3848 = true := by
  rw [show A10K2.u3848 = KTree.node A10K2.u3846 (nat_lit 62204131) (nat_lit 10404645789) (nat_lit 0) A10K2.u3847 from rfl, allE_node, arows3846, irow3848, arows3847]
  all_goals rfl

theorem atot3848 : totK PA10K2 A10K2.u3848 = [0, 0, 0, 1079304815824, 5136790091217, 7928534590815, 4136185391759, 700230614763, 37371994285, 0] := by
  rw [show A10K2.u3848 = KTree.node A10K2.u3846 (nat_lit 62204131) (nat_lit 10404645789) (nat_lit 0) A10K2.u3847 from rfl, totK_node, atot3846, atot3847]
  decide +kernel

theorem arows3853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3853 = true := by
  rw [show A10K2.u3853 = KTree.node A10K2.u3851 (nat_lit 62215509) (nat_lit 6910226604) (nat_lit 0) A10K2.u3852 from rfl, allE_node, arows3851, irow3853, arows3852]
  all_goals rfl

theorem atot3853 : totK PA10K2 A10K2.u3853 = [0, 0, 0, 1559399255615, 6372729151405, 7935557052107, 2974399251052, 317469006064, 6354482628, 0] := by
  rw [show A10K2.u3853 = KTree.node A10K2.u3851 (nat_lit 62215509) (nat_lit 6910226604) (nat_lit 0) A10K2.u3852 from rfl, totK_node, atot3851, atot3852]
  decide +kernel

theorem arows3856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3856 = true := by
  rw [show A10K2.u3856 = KTree.node A10K2.u3854 (nat_lit 62268714) (nat_lit 12578474049) (nat_lit 0) A10K2.u3855 from rfl, allE_node, arows3854, irow3856, arows3855]
  all_goals rfl

theorem atot3856 : totK PA10K2 A10K2.u3856 = [0, 0, 0, 1156618856733, 5419874850337, 7949666620735, 3507421459662, 544900770610, 30429722018, 0] := by
  rw [show A10K2.u3856 = KTree.node A10K2.u3854 (nat_lit 62268714) (nat_lit 12578474049) (nat_lit 0) A10K2.u3855 from rfl, totK_node, atot3854, atot3855]
  decide +kernel

theorem arows3860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3860 = true := by
  rw [show A10K2.u3860 = KTree.node A10K2.u3858 (nat_lit 62278305) (nat_lit 7859361199) (nat_lit 0) A10K2.u3859 from rfl, allE_node, arows3858, irow3860, arows3859]
  all_goals rfl

theorem atot3860 : totK PA10K2 A10K2.u3860 = [0, 0, 0, 840803844797, 4679932927694, 8088740962807, 4262441251750, 670238390316, 17774690686, 0] := by
  rw [show A10K2.u3860 = KTree.node A10K2.u3858 (nat_lit 62278305) (nat_lit 7859361199) (nat_lit 0) A10K2.u3859 from rfl, totK_node, atot3858, atot3859]
  decide +kernel

theorem arows3863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3863 = true := by
  rw [show A10K2.u3863 = KTree.node A10K2.u3861 (nat_lit 62309160) (nat_lit 12102703131) (nat_lit 0) A10K2.u3862 from rfl, allE_node, arows3861, irow3863, arows3862]
  all_goals rfl

theorem atot3863 : totK PA10K2 A10K2.u3863 = [0, 0, 0, 0, 1711012656626, 6840782068990, 7316641858223, 2226254338733, 156494666439, 0] := by
  rw [show A10K2.u3863 = KTree.node A10K2.u3861 (nat_lit 62309160) (nat_lit 12102703131) (nat_lit 0) A10K2.u3862 from rfl, totK_node, atot3861, atot3862]
  decide +kernel

theorem arows3869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3869 = true := by
  rw [show A10K2.u3869 = KTree.node A10K2.u3867 (nat_lit 62918728) (nat_lit 13804082660) (nat_lit 0) A10K2.u3868 from rfl, allE_node, arows3867, irow3869, arows3868]
  all_goals rfl

theorem atot3869 : totK PA10K2 A10K2.u3869 = [0, 1238736264505, 5229187457836, 7423635844095, 3877448416159, 662480438714, 259908348362, 429542201963, 142269073820, 6354482628] := by
  rw [show A10K2.u3869 = KTree.node A10K2.u3867 (nat_lit 62918728) (nat_lit 13804082660) (nat_lit 0) A10K2.u3868 from rfl, totK_node, atot3867, atot3868]
  decide +kernel

theorem arows3872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3872 = true := by
  rw [show A10K2.u3872 = KTree.node A10K2.u3870 (nat_lit 62940828) (nat_lit 8391920921) (nat_lit 0) A10K2.u3871 from rfl, allE_node, arows3870, irow3872, arows3871]
  all_goals rfl

theorem atot3872 : totK PA10K2 A10K2.u3872 = [0, 967120658573, 5028563581981, 8341682291640, 4742382519890, 754958647222, 20158140256, 0, 0, 0] := by
  rw [show A10K2.u3872 = KTree.node A10K2.u3870 (nat_lit 62940828) (nat_lit 8391920921) (nat_lit 0) A10K2.u3871 from rfl, totK_node, atot3870, atot3871]
  decide +kernel

theorem arows3876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3876 = true := by
  rw [show A10K2.u3876 = KTree.node A10K2.u3874 (nat_lit 62951352) (nat_lit 13898329239) (nat_lit 0) A10K2.u3875 from rfl, allE_node, arows3874, irow3876, arows3875]
  all_goals rfl

theorem atot3876 : totK PA10K2 A10K2.u3876 = [0, 0, 1235081951438, 5489755598731, 7934152798788, 3918317500049, 650783974110, 30650496230, 0, 0] := by
  rw [show A10K2.u3876 = KTree.node A10K2.u3874 (nat_lit 62951352) (nat_lit 13898329239) (nat_lit 0) A10K2.u3875 from rfl, totK_node, atot3874, atot3875]
  decide +kernel

theorem arows3879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3879 = true := by
  rw [show A10K2.u3879 = KTree.node A10K2.u3877 (nat_lit 62975964) (nat_lit 1704996572) (nat_lit 0) A10K2.u3878 from rfl, allE_node, arows3877, irow3879, arows3878]
  all_goals rfl

theorem atot3879 : totK PA10K2 A10K2.u3879 = [0, 783941292525, 4133742054390, 7774363832173, 5748924277413, 1360673163101, 83934808191, 0, 0, 0] := by
  rw [show A10K2.u3879 = KTree.node A10K2.u3877 (nat_lit 62975964) (nat_lit 1704996572) (nat_lit 0) A10K2.u3878 from rfl, totK_node, atot3877, atot3878]
  decide +kernel

theorem arows3884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3884 = true := by
  rw [show A10K2.u3884 = KTree.node A10K2.u3882 (nat_lit 63123378) (nat_lit 14335716078) (nat_lit 0) A10K2.u3883 from rfl, allE_node, arows3882, irow3884, arows3883]
  all_goals rfl

theorem atot3884 : totK PA10K2 A10K2.u3884 = [0, 1133570941966, 5185505605616, 8069189374837, 4723126520697, 874515162636, 38912591196, 0, 0, 0] := by
  rw [show A10K2.u3884 = KTree.node A10K2.u3882 (nat_lit 63123378) (nat_lit 14335716078) (nat_lit 0) A10K2.u3883 from rfl, totK_node, atot3882, atot3883]
  decide +kernel

theorem arows3887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3887 = true := by
  rw [show A10K2.u3887 = KTree.node A10K2.u3885 (nat_lit 63143318) (nat_lit 16090923929) (nat_lit 0) A10K2.u3886 from rfl, allE_node, arows3885, irow3887, arows3886]
  all_goals rfl

theorem atot3887 : totK PA10K2 A10K2.u3887 = [0, 327737319032, 2896237099111, 7598780435947, 7073288573886, 1990885340630, 112977250630, 0, 0, 0] := by
  rw [show A10K2.u3887 = KTree.node A10K2.u3885 (nat_lit 63143318) (nat_lit 16090923929) (nat_lit 0) A10K2.u3886 from rfl, totK_node, atot3885, atot3886]
  decide +kernel

theorem arows3891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3891 = true := by
  rw [show A10K2.u3891 = KTree.node A10K2.u3889 (nat_lit 63155770) (nat_lit 11540279771) (nat_lit 0) A10K2.u3890 from rfl, allE_node, arows3889, irow3891, arows3890]
  all_goals rfl

theorem atot3891 : totK PA10K2 A10K2.u3891 = [0, 0, 1132238310523, 5378801741644, 8337776403698, 4493838309309, 623125092835, 13951953716, 0, 0] := by
  rw [show A10K2.u3891 = KTree.node A10K2.u3889 (nat_lit 63155770) (nat_lit 11540279771) (nat_lit 0) A10K2.u3890 from rfl, totK_node, atot3889, atot3890]
  decide +kernel

theorem arows3894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3894 = true := by
  rw [show A10K2.u3894 = KTree.node A10K2.u3892 (nat_lit 63175871) (nat_lit 14180918075) (nat_lit 0) A10K2.u3893 from rfl, allE_node, arows3892, irow3894, arows3893]
  all_goals rfl

theorem atot3894 : totK PA10K2 A10K2.u3894 = [0, 0, 1171954040346, 5106846742815, 7658868456206, 4640902325988, 1012476281932, 61110126106, 0, 0] := by
  rw [show A10K2.u3894 = KTree.node A10K2.u3892 (nat_lit 63175871) (nat_lit 14180918075) (nat_lit 0) A10K2.u3893 from rfl, totK_node, atot3892, atot3893]
  decide +kernel

theorem arows3901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3901 = true := by
  rw [show A10K2.u3901 = KTree.node A10K2.u3899 (nat_lit 63193650) (nat_lit 6208717491) (nat_lit 0) A10K2.u3900 from rfl, allE_node, arows3899, irow3901, arows3900]
  all_goals rfl

theorem atot3901 : totK PA10K2 A10K2.u3901 = [0, 0, 856286534340, 4580812282068, 8057013183681, 4766307070522, 825327296527, 36536693801, 0, 0] := by
  rw [show A10K2.u3901 = KTree.node A10K2.u3899 (nat_lit 63193650) (nat_lit 6208717491) (nat_lit 0) A10K2.u3900 from rfl, totK_node, atot3899, atot3900]
  decide +kernel

theorem arows3904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3904 = true := by
  rw [show A10K2.u3904 = KTree.node A10K2.u3902 (nat_lit 63208605) (nat_lit 1710968333) (nat_lit 0) A10K2.u3903 from rfl, allE_node, arows3902, irow3904, arows3903]
  all_goals rfl

theorem atot3904 : totK PA10K2 A10K2.u3904 = [0, 0, 504850548399, 3600054465710, 7971065633583, 6274927413121, 1438897064965, 73048893714, 0, 0] := by
  rw [show A10K2.u3904 = KTree.node A10K2.u3902 (nat_lit 63208605) (nat_lit 1710968333) (nat_lit 0) A10K2.u3903 from rfl, totK_node, atot3902, atot3903]
  decide +kernel

theorem arows3908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3908 = true := by
  rw [show A10K2.u3908 = KTree.node A10K2.u3906 (nat_lit 63228461) (nat_lit 6398232186) (nat_lit 0) A10K2.u3907 from rfl, allE_node, arows3906, irow3908, arows3907]
  all_goals rfl

theorem atot3908 : totK PA10K2 A10K2.u3908 = [0, 0, 303693864090, 2348151403217, 6528401421487, 7192539913824, 2713131059541, 346664541613, 7903172220, 0] := by
  rw [show A10K2.u3908 = KTree.node A10K2.u3906 (nat_lit 63228461) (nat_lit 6398232186) (nat_lit 0) A10K2.u3907 from rfl, totK_node, atot3906, atot3907]
  decide +kernel

theorem arows3911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3911 = true := by
  rw [show A10K2.u3911 = KTree.node A10K2.u3909 (nat_lit 63380877) (nat_lit 2856238317) (nat_lit 0) A10K2.u3910 from rfl, allE_node, arows3909, irow3911, arows3910]
  all_goals rfl

theorem atot3911 : totK PA10K2 A10K2.u3911 = [0, 0, 1074540657321, 5305233685106, 8407751145079, 4592942558745, 717379293704, 20511962003, 0, 0] := by
  rw [show A10K2.u3911 = KTree.node A10K2.u3909 (nat_lit 63380877) (nat_lit 2856238317) (nat_lit 0) A10K2.u3910 from rfl, totK_node, atot3909, atot3910]
  decide +kernel

theorem arows3916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3916 = true := by
  rw [show A10K2.u3916 = KTree.node A10K2.u3914 (nat_lit 63402043) (nat_lit 5346117577) (nat_lit 0) A10K2.u3915 from rfl, allE_node, arows3914, irow3916, arows3915]
  all_goals rfl

theorem atot3916 : totK PA10K2 A10K2.u3916 = [0, 320479959089, 1798741499838, 4830651596817, 7164090031814, 4784654940390, 1080489751411, 62368562949, 0, 0] := by
  rw [show A10K2.u3916 = KTree.node A10K2.u3914 (nat_lit 63402043) (nat_lit 5346117577) (nat_lit 0) A10K2.u3915 from rfl, totK_node, atot3914, atot3915]
  decide +kernel

theorem arows3919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3919 = true := by
  rw [show A10K2.u3919 = KTree.node A10K2.u3917 (nat_lit 63518756) (nat_lit 13460749187) (nat_lit 0) A10K2.u3918 from rfl, allE_node, arows3917, irow3919, arows3918]
  all_goals rfl

theorem atot3919 : totK PA10K2 A10K2.u3919 = [0, 1184961048737, 5374122431895, 7902576940670, 4174797288074, 703474760981, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3919 = KTree.node A10K2.u3917 (nat_lit 63518756) (nat_lit 13460749187) (nat_lit 0) A10K2.u3918 from rfl, totK_node, atot3917, atot3918]
  decide +kernel

theorem arows3923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3923 = true := by
  rw [show A10K2.u3923 = KTree.node A10K2.u3921 (nat_lit 63532147) (nat_lit 6162812002) (nat_lit 0) A10K2.u3922 from rfl, allE_node, arows3921, irow3923, arows3922]
  all_goals rfl

theorem atot3923 : totK PA10K2 A10K2.u3923 = [0, 800212678090, 4411388030511, 8230120711806, 5415641615353, 1024868819672, 31979841624, 0, 0, 0] := by
  rw [show A10K2.u3923 = KTree.node A10K2.u3921 (nat_lit 63532147) (nat_lit 6162812002) (nat_lit 0) A10K2.u3922 from rfl, totK_node, atot3921, atot3922]
  decide +kernel

theorem arows3926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3926 = true := by
  rw [show A10K2.u3926 = KTree.node A10K2.u3924 (nat_lit 63550693) (nat_lit 6670153125) (nat_lit 0) A10K2.u3925 from rfl, allE_node, arows3924, irow3926, arows3925]
  all_goals rfl

theorem atot3926 : totK PA10K2 A10K2.u3926 = [0, 0, 1238765978493, 5469011682710, 7850525866340, 4014303180600, 673614027237, 31082886609, 0, 0] := by
  rw [show A10K2.u3926 = KTree.node A10K2.u3924 (nat_lit 63550693) (nat_lit 6670153125) (nat_lit 0) A10K2.u3925 from rfl, totK_node, atot3924, atot3925]
  decide +kernel

theorem arows3932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3932 = true := by
  rw [show A10K2.u3932 = KTree.node A10K2.u3930 (nat_lit 63563186) (nat_lit 14764739583) (nat_lit 0) A10K2.u3931 from rfl, allE_node, arows3930, irow3932, arows3931]
  all_goals rfl

theorem atot3932 : totK PA10K2 A10K2.u3932 = [0, 575843650046, 2998071613641, 6318333798061, 6643498034516, 2656767624848, 286939104731, 6121173289, 0, 0] := by
  rw [show A10K2.u3932 = KTree.node A10K2.u3930 (nat_lit 63563186) (nat_lit 14764739583) (nat_lit 0) A10K2.u3931 from rfl, totK_node, atot3930, atot3931]
  decide +kernel

theorem arows3935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3935 = true := by
  rw [show A10K2.u3935 = KTree.node A10K2.u3933 (nat_lit 63586346) (nat_lit 7801927156) (nat_lit 0) A10K2.u3934 from rfl, allE_node, arows3933, irow3935, arows3934]
  all_goals rfl

theorem atot3935 : totK PA10K2 A10K2.u3935 = [0, 962728796160, 5031976804784, 8233141786562, 4521754484933, 720467252225, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3935 = KTree.node A10K2.u3933 (nat_lit 63586346) (nat_lit 7801927156) (nat_lit 0) A10K2.u3934 from rfl, totK_node, atot3933, atot3934]
  decide +kernel

theorem arows3939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3939 = true := by
  rw [show A10K2.u3939 = KTree.node A10K2.u3937 (nat_lit 63619171) (nat_lit 4730707309) (nat_lit 0) A10K2.u3938 from rfl, allE_node, arows3937, irow3939, arows3938]
  all_goals rfl

theorem atot3939 : totK PA10K2 A10K2.u3939 = [0, 0, 1705257138845, 7030952744575, 8023974045751, 2291413431934, 141227747431, 0, 0, 0] := by
  rw [show A10K2.u3939 = KTree.node A10K2.u3937 (nat_lit 63619171) (nat_lit 4730707309) (nat_lit 0) A10K2.u3938 from rfl, totK_node, atot3937, atot3938]
  decide +kernel

theorem arows3942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3942 = true := by
  rw [show A10K2.u3942 = KTree.node A10K2.u3940 (nat_lit 63642724) (nat_lit 4971836254) (nat_lit 0) A10K2.u3941 from rfl, allE_node, arows3940, irow3942, arows3941]
  all_goals rfl

theorem atot3942 : totK PA10K2 A10K2.u3942 = [0, 1360874852670, 5668560569300, 7684375306903, 4016779987527, 1025297237059, 145541592289, 6354482628, 0, 0] := by
  rw [show A10K2.u3942 = KTree.node A10K2.u3940 (nat_lit 63642724) (nat_lit 4971836254) (nat_lit 0) A10K2.u3941 from rfl, totK_node, atot3940, atot3941]
  decide +kernel

theorem arows3947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3947 = true := by
  rw [show A10K2.u3947 = KTree.node A10K2.u3945 (nat_lit 63661723) (nat_lit 10032468677) (nat_lit 0) A10K2.u3946 from rfl, allE_node, arows3945, irow3947, arows3946]
  all_goals rfl

theorem atot3947 : totK PA10K2 A10K2.u3947 = [0, 862423573369, 4480688564452, 7971757448093, 5354687430768, 1098428814285, 45563282859, 0, 0, 0] := by
  rw [show A10K2.u3947 = KTree.node A10K2.u3945 (nat_lit 63661723) (nat_lit 10032468677) (nat_lit 0) A10K2.u3946 from rfl, totK_node, atot3945, atot3946]
  decide +kernel

theorem arows3950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3950 = true := by
  rw [show A10K2.u3950 = KTree.node A10K2.u3948 (nat_lit 63672752) (nat_lit 14711657310) (nat_lit 0) A10K2.u3949 from rfl, allE_node, arows3948, irow3950, arows3949]
  all_goals rfl

theorem atot3950 : totK PA10K2 A10K2.u3950 = [0, 0, 1586444847211, 6408430054403, 8138060831707, 3449044218671, 382181709662, 6904928264, 0, 0] := by
  rw [show A10K2.u3950 = KTree.node A10K2.u3948 (nat_lit 63672752) (nat_lit 14711657310) (nat_lit 0) A10K2.u3949 from rfl, totK_node, atot3948, atot3949]
  decide +kernel

theorem arows3954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3954 = true := by
  rw [show A10K2.u3954 = KTree.node A10K2.u3952 (nat_lit 63694278) (nat_lit 15767512791) (nat_lit 0) A10K2.u3953 from rfl, allE_node, arows3952, irow3954, arows3953]
  all_goals rfl

theorem atot3954 : totK PA10K2 A10K2.u3954 = [0, 0, 861712836175, 4714065169658, 8299347770158, 5090960576914, 798178039828, 19271132487, 0, 0] := by
  rw [show A10K2.u3954 = KTree.node A10K2.u3952 (nat_lit 63694278) (nat_lit 15767512791) (nat_lit 0) A10K2.u3953 from rfl, totK_node, atot3952, atot3953]
  decide +kernel

theorem arows3957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3957 = true := by
  rw [show A10K2.u3957 = KTree.node A10K2.u3955 (nat_lit 63778190) (nat_lit 14990984084) (nat_lit 0) A10K2.u3956 from rfl, allE_node, arows3955, irow3957, arows3956]
  all_goals rfl

theorem atot3957 : totK PA10K2 A10K2.u3957 = [0, 0, 947131156545, 4589996821107, 7668540558266, 5013761887017, 1175209683318, 80654767924, 0, 0] := by
  rw [show A10K2.u3957 = KTree.node A10K2.u3955 (nat_lit 63778190) (nat_lit 14990984084) (nat_lit 0) A10K2.u3956 from rfl, totK_node, atot3955, atot3956]
  decide +kernel

theorem arows3965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3965 = true := by
  rw [show A10K2.u3965 = KTree.node A10K2.u3963 (nat_lit 63789932) (nat_lit 11820436177) (nat_lit 0) A10K2.u3964 from rfl, allE_node, arows3963, irow3965, arows3964]
  all_goals rfl

theorem atot3965 : totK PA10K2 A10K2.u3965 = [0, 0, 1356567296292, 5907566926692, 8286340639199, 3717944098393, 410247618964, 6239673734, 0, 0] := by
  rw [show A10K2.u3965 = KTree.node A10K2.u3963 (nat_lit 63789932) (nat_lit 11820436177) (nat_lit 0) A10K2.u3964 from rfl, totK_node, atot3963, atot3964]
  decide +kernel

theorem arows3968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3968 = true := by
  rw [show A10K2.u3968 = KTree.node A10K2.u3966 (nat_lit 63809877) (nat_lit 6960785344) (nat_lit 0) A10K2.u3967 from rfl, allE_node, arows3966, irow3968, arows3967]
  all_goals rfl

theorem atot3968 : totK PA10K2 A10K2.u3968 = [0, 0, 0, 1345715116141, 5784709004159, 7797279946420, 3672158012771, 605684852121, 31018567651, 0] := by
  rw [show A10K2.u3968 = KTree.node A10K2.u3966 (nat_lit 63809877) (nat_lit 6960785344) (nat_lit 0) A10K2.u3967 from rfl, totK_node, atot3966, atot3967]
  decide +kernel

theorem arows3972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3972 = true := by
  rw [show A10K2.u3972 = KTree.node A10K2.u3970 (nat_lit 63822112) (nat_lit 12452220759) (nat_lit 0) A10K2.u3971 from rfl, allE_node, arows3970, irow3972, arows3971]
  all_goals rfl

theorem atot3972 : totK PA10K2 A10K2.u3972 = [0, 0, 308899695994, 2372603126195, 6411482747779, 7206480593085, 2759514211645, 306401515452, 5685526223, 0] := by
  rw [show A10K2.u3972 = KTree.node A10K2.u3970 (nat_lit 63822112) (nat_lit 12452220759) (nat_lit 0) A10K2.u3971 from rfl, totK_node, atot3970, atot3971]
  decide +kernel

theorem arows3975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3975 = true := by
  rw [show A10K2.u3975 = KTree.node A10K2.u3973 (nat_lit 63846693) (nat_lit 7473897057) (nat_lit 0) A10K2.u3974 from rfl, allE_node, arows3973, irow3975, arows3974]
  all_goals rfl

theorem atot3975 : totK PA10K2 A10K2.u3975 = [0, 0, 1229205815242, 5525472622260, 7991593773184, 4025497900367, 654459163522, 31768748853, 0, 0] := by
  rw [show A10K2.u3975 = KTree.node A10K2.u3973 (nat_lit 63846693) (nat_lit 7473897057) (nat_lit 0) A10K2.u3974 from rfl, totK_node, atot3973, atot3974]
  decide +kernel

theorem arows3980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3980 = true := by
  rw [show A10K2.u3980 = KTree.node A10K2.u3978 (nat_lit 63875882) (nat_lit 11799158058) (nat_lit 0) A10K2.u3979 from rfl, allE_node, arows3978, irow3980, arows3979]
  all_goals rfl

theorem atot3980 : totK PA10K2 A10K2.u3980 = [0, 0, 0, 2196059674886, 7735956367234, 7391500377882, 1685829468266, 82893760668, 0, 0] := by
  rw [show A10K2.u3980 = KTree.node A10K2.u3978 (nat_lit 63875882) (nat_lit 11799158058) (nat_lit 0) A10K2.u3979 from rfl, totK_node, atot3978, atot3979]
  decide +kernel

theorem arows3983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3983 = true := by
  rw [show A10K2.u3983 = KTree.node A10K2.u3981 (nat_lit 63901794) (nat_lit 11933677) (nat_lit 0) A10K2.u3982 from rfl, allE_node, arows3981, irow3983, arows3982]
  all_goals rfl

theorem atot3983 : totK PA10K2 A10K2.u3983 = [0, 0, 1360384191650, 5277036370995, 7035842855131, 4384370586029, 1411410693479, 196172791120, 6239673734, 0] := by
  rw [show A10K2.u3983 = KTree.node A10K2.u3981 (nat_lit 63901794) (nat_lit 11933677) (nat_lit 0) A10K2.u3982 from rfl, totK_node, atot3981, atot3982]
  decide +kernel

theorem arows3987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3987 = true := by
  rw [show A10K2.u3987 = KTree.node A10K2.u3985 (nat_lit 63922806) (nat_lit 15283806720) (nat_lit 0) A10K2.u3986 from rfl, allE_node, arows3985, irow3987, arows3986]
  all_goals rfl

theorem atot3987 : totK PA10K2 A10K2.u3987 = [0, 0, 861932599948, 4633573469250, 8208390341750, 5140354447657, 915534113181, 37566863252, 0, 0] := by
  rw [show A10K2.u3987 = KTree.node A10K2.u3985 (nat_lit 63922806) (nat_lit 15283806720) (nat_lit 0) A10K2.u3986 from rfl, totK_node, atot3985, atot3986]
  decide +kernel

theorem arows3990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3990 = true := by
  rw [show A10K2.u3990 = KTree.node A10K2.u3988 (nat_lit 64490309) (nat_lit 6811197171) (nat_lit 0) A10K2.u3989 from rfl, allE_node, arows3988, irow3990, arows3989]
  all_goals rfl

theorem atot3990 : totK PA10K2 A10K2.u3990 = [0, 887742285343, 3884863129790, 6268875732501, 5089702715757, 2773510872738, 781053519867, 56100664475, 0, 0] := by
  rw [show A10K2.u3990 = KTree.node A10K2.u3988 (nat_lit 64490309) (nat_lit 6811197171) (nat_lit 0) A10K2.u3989 from rfl, totK_node, atot3988, atot3989]
  decide +kernel

theorem arows3996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3996 = true := by
  rw [show A10K2.u3996 = KTree.node A10K2.u3994 (nat_lit 64515547) (nat_lit 6673012401) (nat_lit 0) A10K2.u3995 from rfl, allE_node, arows3994, irow3996, arows3995]
  all_goals rfl

theorem atot3996 : totK PA10K2 A10K2.u3996 = [0, 982976898703, 4867153703228, 8017869501642, 5162630695714, 1140173821339, 62979767238, 0, 0, 0] := by
  rw [show A10K2.u3996 = KTree.node A10K2.u3994 (nat_lit 64515547) (nat_lit 6673012401) (nat_lit 0) A10K2.u3995 from rfl, totK_node, atot3994, atot3995]
  decide +kernel

theorem arows3999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3999 = true := by
  rw [show A10K2.u3999 = KTree.node A10K2.u3997 (nat_lit 64525088) (nat_lit 13294287949) (nat_lit 0) A10K2.u3998 from rfl, allE_node, arows3997, irow3999, arows3998]
  all_goals rfl

theorem atot3999 : totK PA10K2 A10K2.u3999 = [0, 0, 1310902324575, 5835116685287, 8048388746250, 3666631584520, 521950966461, 13364899180, 0, 0] := by
  rw [show A10K2.u3999 = KTree.node A10K2.u3997 (nat_lit 64525088) (nat_lit 13294287949) (nat_lit 0) A10K2.u3998 from rfl, totK_node, atot3997, atot3998]
  decide +kernel

theorem arows4003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4003 = true := by
  rw [show A10K2.u4003 = KTree.node A10K2.u4001 (nat_lit 64563869) (nat_lit 5871199034) (nat_lit 0) A10K2.u4002 from rfl, allE_node, arows4001, irow4003, arows4002]
  all_goals rfl

theorem atot4003 : totK PA10K2 A10K2.u4003 = [0, 823020947679, 4268110526024, 7697849708784, 5589206906194, 1401520600906, 89319918621, 0, 0, 0] := by
  rw [show A10K2.u4003 = KTree.node A10K2.u4001 (nat_lit 64563869) (nat_lit 5871199034) (nat_lit 0) A10K2.u4002 from rfl, totK_node, atot4001, atot4002]
  decide +kernel

theorem arows4006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4006 = true := by
  rw [show A10K2.u4006 = KTree.node A10K2.u4004 (nat_lit 64578080) (nat_lit 13874073305) (nat_lit 0) A10K2.u4005 from rfl, allE_node, arows4004, irow4006, arows4005]
  all_goals rfl

theorem atot4006 : totK PA10K2 A10K2.u4006 = [0, 1310713848065, 5763493098128, 8227333323046, 4072173771750, 580806816655, 13206187354, 0, 0, 0] := by
  rw [show A10K2.u4006 = KTree.node A10K2.u4004 (nat_lit 64578080) (nat_lit 13874073305) (nat_lit 0) A10K2.u4005 from rfl, totK_node, atot4004, atot4005]
  decide +kernel

theorem arows4011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4011 = true := by
  rw [show A10K2.u4011 = KTree.node A10K2.u4009 (nat_lit 64596670) (nat_lit 14259089565) (nat_lit 0) A10K2.u4010 from rfl, allE_node, arows4009, irow4011, arows4010]
  all_goals rfl

theorem atot4011 : totK PA10K2 A10K2.u4011 = [0, 0, 1255655858750, 5636572953507, 8045482486912, 3936675534059, 641446773724, 31082886609, 0, 0] := by
  rw [show A10K2.u4011 = KTree.node A10K2.u4009 (nat_lit 64596670) (nat_lit 14259089565) (nat_lit 0) A10K2.u4010 from rfl, totK_node, atot4009, atot4010]
  decide +kernel

theorem arows4014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4014 = true := by
  rw [show A10K2.u4014 = KTree.node A10K2.u4012 (nat_lit 64611255) (nat_lit 15026248115) (nat_lit 0) A10K2.u4013 from rfl, allE_node, arows4012, irow4014, arows4013]
  all_goals rfl

theorem atot4014 : totK PA10K2 A10K2.u4014 = [0, 383428828220, 2578228661072, 6526477705333, 7043286909685, 2736878438131, 310936789450, 6121173289, 0, 0] := by
  rw [show A10K2.u4014 = KTree.node A10K2.u4012 (nat_lit 64611255) (nat_lit 15026248115) (nat_lit 0) A10K2.u4013 from rfl, totK_node, atot4012, atot4013]
  decide +kernel

theorem arows4018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4018 = true := by
  rw [show A10K2.u4018 = KTree.node A10K2.u4016 (nat_lit 64693412) (nat_lit 11907105070) (nat_lit 0) A10K2.u4017 from rfl, allE_node, arows4016, irow4018, arows4017]
  all_goals rfl

theorem atot4018 : totK PA10K2 A10K2.u4018 = [0, 1112250661790, 5243432639141, 8073842739824, 4431442065861, 754475014708, 33596182596, 0, 0, 0] := by
  rw [show A10K2.u4018 = KTree.node A10K2.u4016 (nat_lit 64693412) (nat_lit 11907105070) (nat_lit 0) A10K2.u4017 from rfl, totK_node, atot4016, atot4017]
  decide +kernel

theorem arows4021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4021 = true := by
  rw [show A10K2.u4021 = KTree.node A10K2.u4019 (nat_lit 64711751) (nat_lit 11210411356) (nat_lit 0) A10K2.u4020 from rfl, allE_node, arows4019, irow4021, arows4020]
  all_goals rfl

theorem atot4021 : totK PA10K2 A10K2.u4021 = [0, 893325715942, 4643264014959, 8162793158009, 5247465308921, 931342119836, 30099889814, 0, 0, 0] := by
  rw [show A10K2.u4021 = KTree.node A10K2.u4019 (nat_lit 64711751) (nat_lit 11210411356) (nat_lit 0) A10K2.u4020 from rfl, totK_node, atot4019, atot4020]
  decide +kernel

theorem arows4028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4028 = true := by
  rw [show A10K2.u4028 = KTree.node A10K2.u4026 (nat_lit 64721009) (nat_lit 8338721639) (nat_lit 0) A10K2.u4027 from rfl, allE_node, arows4026, irow4028, arows4027]
  all_goals rfl

theorem atot4028 : totK PA10K2 A10K2.u4028 = [0, 0, 1374540130630, 5938368022549, 8122868505629, 3594110790173, 406314759914, 6904928264, 0, 0] := by
  rw [show A10K2.u4028 = KTree.node A10K2.u4026 (nat_lit 64721009) (nat_lit 8338721639) (nat_lit 0) A10K2.u4027 from rfl, totK_node, atot4026, atot4027]
  decide +kernel

theorem arows4031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4031 = true := by
  rw [show A10K2.u4031 = KTree.node A10K2.u4029 (nat_lit 64742326) (nat_lit 16784593185) (nat_lit 0) A10K2.u4030 from rfl, allE_node, arows4029, irow4031, arows4030]
  all_goals rfl

theorem atot4031 : totK PA10K2 A10K2.u4031 = [0, 0, 1011139790529, 5187142165941, 8431885064745, 4595468534086, 613824480836, 13113983930, 0, 0] := by
  rw [show A10K2.u4031 = KTree.node A10K2.u4029 (nat_lit 64742326) (nat_lit 16784593185) (nat_lit 0) A10K2.u4030 from rfl, totK_node, atot4029, atot4030]
  decide +kernel

theorem arows4035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4035 = true := by
  rw [show A10K2.u4035 = KTree.node A10K2.u4033 (nat_lit 64752758) (nat_lit 16190745451) (nat_lit 0) A10K2.u4034 from rfl, allE_node, arows4033, irow4035, arows4034]
  all_goals rfl

theorem atot4035 : totK PA10K2 A10K2.u4035 = [0, 0, 1042699786101, 4615920726299, 7556352058520, 5200191951448, 1210662418170, 68408066808, 0, 0] := by
  rw [show A10K2.u4035 = KTree.node A10K2.u4033 (nat_lit 64752758) (nat_lit 16190745451) (nat_lit 0) A10K2.u4034 from rfl, totK_node, atot4033, atot4034]
  decide +kernel

theorem arows4038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4038 = true := by
  rw [show A10K2.u4038 = KTree.node A10K2.u4036 (nat_lit 64777914) (nat_lit 14617708444) (nat_lit 0) A10K2.u4037 from rfl, allE_node, arows4036, irow4038, arows4037]
  all_goals rfl

theorem atot4038 : totK PA10K2 A10K2.u4038 = [0, 0, 826016771734, 4624473019323, 8246508203012, 5270787365299, 1110280591965, 62351816811, 0, 0] := by
  rw [show A10K2.u4038 = KTree.node A10K2.u4036 (nat_lit 64777914) (nat_lit 14617708444) (nat_lit 0) A10K2.u4037 from rfl, totK_node, atot4036, atot4037]
  decide +kernel

theorem arows4043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4043 = true := by
  rw [show A10K2.u4043 = KTree.node A10K2.u4041 (nat_lit 64789568) (nat_lit 15408252699) (nat_lit 0) A10K2.u4042 from rfl, allE_node, arows4041, irow4043, arows4042]
  all_goals rfl

theorem atot4043 : totK PA10K2 A10K2.u4043 = [0, 0, 0, 1668844816530, 6847858425211, 8260066982834, 2844189669629, 275314874885, 7007974415, 0] := by
  rw [show A10K2.u4043 = KTree.node A10K2.u4041 (nat_lit 64789568) (nat_lit 15408252699) (nat_lit 0) A10K2.u4042 from rfl, totK_node, atot4041, atot4042]
  decide +kernel

theorem arows4046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4046 = true := by
  rw [show A10K2.u4046 = KTree.node A10K2.u4044 (nat_lit 64828601) (nat_lit 4071480855) (nat_lit 0) A10K2.u4045 from rfl, allE_node, arows4044, irow4046, arows4045]
  all_goals rfl

theorem atot4046 : totK PA10K2 A10K2.u4046 = [0, 0, 1228023864193, 5154710477804, 7520091625132, 4518704678126, 1068028620232, 75027878843, 0, 0] := by
  rw [show A10K2.u4046 = KTree.node A10K2.u4044 (nat_lit 64828601) (nat_lit 4071480855) (nat_lit 0) A10K2.u4045 from rfl, totK_node, atot4044, atot4045]
  decide +kernel

theorem arows4050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4050 = true := by
  rw [show A10K2.u4050 = KTree.node A10K2.u4048 (nat_lit 64842870) (nat_lit 16353907351) (nat_lit 0) A10K2.u4049 from rfl, allE_node, arows4048, irow4050, arows4049]
  all_goals rfl

theorem atot4050 : totK PA10K2 A10K2.u4050 = [0, 0, 903713312809, 4771226518052, 8312894790586, 5145251719359, 908088702249, 25326886324, 0, 0] := by
  rw [show A10K2.u4050 = KTree.node A10K2.u4048 (nat_lit 64842870) (nat_lit 16353907351) (nat_lit 0) A10K2.u4049 from rfl, totK_node, atot4048, atot4049]
  decide +kernel

theorem arows4053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4053 = true := by
  rw [show A10K2.u4053 = KTree.node A10K2.u4051 (nat_lit 64861466) (nat_lit 14745446160) (nat_lit 0) A10K2.u4052 from rfl, allE_node, arows4051, irow4053, arows4052]
  all_goals rfl

theorem atot4053 : totK PA10K2 A10K2.u4053 = [0, 0, 0, 1626907220786, 6347890679669, 7926640728484, 3309338105376, 391503503061, 7151180950, 0] := by
  rw [show A10K2.u4053 = KTree.node A10K2.u4051 (nat_lit 64861466) (nat_lit 14745446160) (nat_lit 0) A10K2.u4052 from rfl, totK_node, atot4051, atot4052]
  decide +kernel

theorem arows4059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4059 = true := by
  rw [show A10K2.u4059 = KTree.node A10K2.u4057 (nat_lit 64948998) (nat_lit 8595300719) (nat_lit 0) A10K2.u4058 from rfl, allE_node, arows4057, irow4059, arows4058]
  all_goals rfl

theorem atot4059 : totK PA10K2 A10K2.u4059 = [0, 0, 913533399860, 4368751630711, 7496723211510, 5380781427763, 1306383730739, 74623879111, 0, 0] := by
  rw [show A10K2.u4059 = KTree.node A10K2.u4057 (nat_lit 64948998) (nat_lit 8595300719) (nat_lit 0) A10K2.u4058 from rfl, totK_node, atot4057, atot4058]
  decide +kernel

theorem arows4062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4062 = true := by
  rw [show A10K2.u4062 = KTree.node A10K2.u4060 (nat_lit 64960722) (nat_lit 15339778260) (nat_lit 0) A10K2.u4061 from rfl, allE_node, arows4060, irow4062, arows4061]
  all_goals rfl

theorem atot4062 : totK PA10K2 A10K2.u4062 = [0, 0, 1472487061390, 6004988022205, 8024364917871, 3851302495769, 536024263293, 12219140272, 0, 0] := by
  rw [show A10K2.u4062 = KTree.node A10K2.u4060 (nat_lit 64960722) (nat_lit 15339778260) (nat_lit 0) A10K2.u4061 from rfl, totK_node, atot4060, atot4061]
  decide +kernel

theorem arows4066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4066 = true := by
  rw [show A10K2.u4066 = KTree.node A10K2.u4064 (nat_lit 64978843) (nat_lit 7927819500) (nat_lit 0) A10K2.u4065 from rfl, allE_node, arows4064, irow4066, arows4065]
  all_goals rfl

theorem atot4066 : totK PA10K2 A10K2.u4066 = [0, 0, 0, 1983479647724, 7083776796015, 7723077113541, 2627354179598, 267896749353, 6318667960, 0] := by
  rw [show A10K2.u4066 = KTree.node A10K2.u4064 (nat_lit 64978843) (nat_lit 7927819500) (nat_lit 0) A10K2.u4065 from rfl, totK_node, atot4064, atot4065]
  decide +kernel

theorem arows4069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4069 = true := by
  rw [show A10K2.u4069 = KTree.node A10K2.u4067 (nat_lit 64992421) (nat_lit 6192536777) (nat_lit 0) A10K2.u4068 from rfl, allE_node, arows4067, irow4069, arows4068]
  all_goals rfl

theorem atot4069 : totK PA10K2 A10K2.u4069 = [0, 0, 0, 1380984628533, 6019076200673, 8276457840518, 3667880158807, 391066797628, 6439430839, 0] := by
  rw [show A10K2.u4069 = KTree.node A10K2.u4067 (nat_lit 64992421) (nat_lit 6192536777) (nat_lit 0) A10K2.u4068 from rfl, totK_node, atot4067, atot4068]
  decide +kernel

theorem arows4074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4074 = true := by
  rw [show A10K2.u4074 = KTree.node A10K2.u4072 (nat_lit 65011192) (nat_lit 13102863679) (nat_lit 0) A10K2.u4073 from rfl, allE_node, arows4072, irow4074, arows4073]
  all_goals rfl

theorem atot4074 : totK PA10K2 A10K2.u4074 = [869984120561, 3103308310460, 3170048165460, 1148543360872, 2025716170933, 4508958694298, 3740560321955, 961189328672, 61018386929, 0] := by
  rw [show A10K2.u4074 = KTree.node A10K2.u4072 (nat_lit 65011192) (nat_lit 13102863679) (nat_lit 0) A10K2.u4073 from rfl, totK_node, atot4072, atot4073]
  decide +kernel

theorem arows4077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4077 = true := by
  rw [show A10K2.u4077 = KTree.node A10K2.u4075 (nat_lit 67126020) (nat_lit 12986382215) (nat_lit 0) A10K2.u4076 from rfl, allE_node, arows4075, irow4077, arows4076]
  all_goals rfl

theorem atot4077 : totK PA10K2 A10K2.u4077 = [727164550710, 4305298642635, 8056905358996, 4916363458824, 809173961335, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4077 = KTree.node A10K2.u4075 (nat_lit 67126020) (nat_lit 12986382215) (nat_lit 0) A10K2.u4076 from rfl, totK_node, atot4075, atot4076]
  decide +kernel

theorem arows4081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4081 = true := by
  rw [show A10K2.u4081 = KTree.node A10K2.u4079 (nat_lit 67138102) (nat_lit 16046309405) (nat_lit 0) A10K2.u4080 from rfl, allE_node, arows4079, irow4081, arows4080]
  all_goals rfl

theorem atot4081 : totK PA10K2 A10K2.u4081 = [741544312551, 4045647454938, 7615555359188, 5702821104228, 1437369506636, 87262586715, 0, 0, 0, 0] := by
  rw [show A10K2.u4081 = KTree.node A10K2.u4079 (nat_lit 67138102) (nat_lit 16046309405) (nat_lit 0) A10K2.u4080 from rfl, totK_node, atot4079, atot4080]
  decide +kernel

theorem arows4084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4084 = true := by
  rw [show A10K2.u4084 = KTree.node A10K2.u4082 (nat_lit 67148900) (nat_lit 11270294587) (nat_lit 0) A10K2.u4083 from rfl, allE_node, arows4082, irow4084, arows4083]
  all_goals rfl

theorem atot4084 : totK PA10K2 A10K2.u4084 = [0, 1011121622700, 5228145755536, 8057869458836, 3925647054197, 626612387376, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4084 = KTree.node A10K2.u4082 (nat_lit 67148900) (nat_lit 11270294587) (nat_lit 0) A10K2.u4083 from rfl, totK_node, atot4082, atot4083]
  decide +kernel

theorem arows4097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4097 = true := by
  rw [show A10K2.u4097 = KTree.node A10K2.u4095 (nat_lit 67170235) (nat_lit 6693528479) (nat_lit 0) A10K2.u4096 from rfl, allE_node, arows4095, irow4097, arows4096]
  all_goals rfl

theorem atot4097 : totK PA10K2 A10K2.u4097 = [797268155618, 3954278090583, 6971781933622, 5527182862104, 1950723776971, 229278597239, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4097 = KTree.node A10K2.u4095 (nat_lit 67170235) (nat_lit 6693528479) (nat_lit 0) A10K2.u4096 from rfl, totK_node, atot4095, atot4096]
  decide +kernel

theorem arows4100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4100 = true := by
  rw [show A10K2.u4100 = KTree.node A10K2.u4098 (nat_lit 67253416) (nat_lit 6100920433) (nat_lit 0) A10K2.u4099 from rfl, allE_node, arows4098, irow4100, arows4099]
  all_goals rfl

theorem atot4100 : totK PA10K2 A10K2.u4100 = [1060292705054, 4623433113943, 7338130150948, 4815857098291, 1066826879419, 62600422739, 0, 0, 0, 0] := by
  rw [show A10K2.u4100 = KTree.node A10K2.u4098 (nat_lit 67253416) (nat_lit 6100920433) (nat_lit 0) A10K2.u4099 from rfl, totK_node, atot4098, atot4099]
  decide +kernel

theorem arows4104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4104 = true := by
  rw [show A10K2.u4104 = KTree.node A10K2.u4102 (nat_lit 67273270) (nat_lit 15342451940) (nat_lit 0) A10K2.u4103 from rfl, allE_node, arows4102, irow4104, arows4103]
  all_goals rfl

theorem atot4104 : totK PA10K2 A10K2.u4104 = [198880611318, 2938303901762, 7869038524950, 6498133274920, 1471176792202, 71254002758, 0, 0, 0, 0] := by
  rw [show A10K2.u4104 = KTree.node A10K2.u4102 (nat_lit 67273270) (nat_lit 15342451940) (nat_lit 0) A10K2.u4103 from rfl, totK_node, atot4102, atot4103]
  decide +kernel

theorem arows4107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4107 = true := by
  rw [show A10K2.u4107 = KTree.node A10K2.u4105 (nat_lit 67294384) (nat_lit 11933677) (nat_lit 0) A10K2.u4106 from rfl, allE_node, arows4105, irow4107, arows4106]
  all_goals rfl

theorem atot4107 : totK PA10K2 A10K2.u4107 = [809589589006, 3358144618084, 5991128833196, 5945371100415, 2406723119458, 322395268869, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4107 = KTree.node A10K2.u4105 (nat_lit 67294384) (nat_lit 11933677) (nat_lit 0) A10K2.u4106 from rfl, totK_node, atot4105, atot4106]
  decide +kernel

theorem arows4112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4112 = true := by
  rw [show A10K2.u4112 = KTree.node A10K2.u4110 (nat_lit 67317253) (nat_lit 4509100275) (nat_lit 0) A10K2.u4111 from rfl, allE_node, arows4110, irow4112, arows4111]
  all_goals rfl

theorem atot4112 : totK PA10K2 A10K2.u4112 = [1078827900697, 5244882593153, 8371047101519, 4645550825044, 749532751775, 30810868011, 0, 0, 0, 0] := by
  rw [show A10K2.u4112 = KTree.node A10K2.u4110 (nat_lit 67317253) (nat_lit 4509100275) (nat_lit 0) A10K2.u4111 from rfl, totK_node, atot4110, atot4111]
  decide +kernel

theorem arows4115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4115 = true := by
  rw [show A10K2.u4115 = KTree.node A10K2.u4113 (nat_lit 67338581) (nat_lit 6249061319) (nat_lit 0) A10K2.u4114 from rfl, allE_node, arows4113, irow4115, arows4114]
  all_goals rfl

theorem atot4115 : totK PA10K2 A10K2.u4115 = [0, 1795355414758, 6727171704277, 7879341908493, 3099992551948, 351856086650, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4115 = KTree.node A10K2.u4113 (nat_lit 67338581) (nat_lit 6249061319) (nat_lit 0) A10K2.u4114 from rfl, totK_node, atot4113, atot4114]
  decide +kernel

theorem arows4119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4119 = true := by
  rw [show A10K2.u4119 = KTree.node A10K2.u4117 (nat_lit 67363775) (nat_lit 14174167974) (nat_lit 0) A10K2.u4118 from rfl, allE_node, arows4117, irow4119, arows4118]
  all_goals rfl

theorem atot4119 : totK PA10K2 A10K2.u4119 = [0, 1077250908890, 5312712917854, 8464385829587, 4638014731652, 646245169538, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u4119 = KTree.node A10K2.u4117 (nat_lit 67363775) (nat_lit 14174167974) (nat_lit 0) A10K2.u4118 from rfl, totK_node, atot4117, atot4118]
  decide +kernel

theorem arows4122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4122 = true := by
  rw [show A10K2.u4122 = KTree.node A10K2.u4120 (nat_lit 67374522) (nat_lit 13098910014) (nat_lit 0) A10K2.u4121 from rfl, allE_node, arows4120, irow4122, arows4121]
  all_goals rfl

theorem atot4122 : totK PA10K2 A10K2.u4122 = [0, 1080359536170, 4749036268392, 7439699916802, 4740556605402, 1126110707058, 79717692957, 0, 0, 0] := by
  rw [show A10K2.u4122 = KTree.node A10K2.u4120 (nat_lit 67374522) (nat_lit 13098910014) (nat_lit 0) A10K2.u4121 from rfl, totK_node, atot4120, atot4121]
  decide +kernel

theorem arows4128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4128 = true := by
  rw [show A10K2.u4128 = KTree.node A10K2.u4126 (nat_lit 67393837) (nat_lit 6651382109) (nat_lit 0) A10K2.u4127 from rfl, allE_node, arows4126, irow4128, arows4127]
  all_goals rfl

theorem atot4128 : totK PA10K2 A10K2.u4128 = [0, 1254172466427, 5794537123692, 8168796409034, 3448658435833, 339110983489, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u4128 = KTree.node A10K2.u4126 (nat_lit 67393837) (nat_lit 6651382109) (nat_lit 0) A10K2.u4127 from rfl, totK_node, atot4126, atot4127]
  decide +kernel

theorem arows4131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4131 = true := by
  rw [show A10K2.u4131 = KTree.node A10K2.u4129 (nat_lit 67406178) (nat_lit 10610376041) (nat_lit 0) A10K2.u4130 from rfl, allE_node, arows4129, irow4131, arows4130]
  all_goals rfl

theorem atot4131 : totK PA10K2 A10K2.u4131 = [0, 0, 1368053363640, 5835580855523, 7738895307649, 3511483777604, 587846535122, 30605747850, 0, 0] := by
  rw [show A10K2.u4131 = KTree.node A10K2.u4129 (nat_lit 67406178) (nat_lit 10610376041) (nat_lit 0) A10K2.u4130 from rfl, totK_node, atot4129, atot4130]
  decide +kernel

theorem arows4135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4135 = true := by
  rw [show A10K2.u4135 = KTree.node A10K2.u4133 (nat_lit 67426316) (nat_lit 11759478708) (nat_lit 0) A10K2.u4134 from rfl, allE_node, arows4133, irow4135, arows4134]
  all_goals rfl

theorem atot4135 : totK PA10K2 A10K2.u4135 = [0, 237700837005, 2034038347140, 6200842814153, 7355696465792, 2688483022980, 294486695396, 5528811039, 0, 0] := by
  rw [show A10K2.u4135 = KTree.node A10K2.u4133 (nat_lit 67426316) (nat_lit 11759478708) (nat_lit 0) A10K2.u4134 from rfl, totK_node, atot4133, atot4134]
  decide +kernel

theorem arows4138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4138 = true := by
  rw [show A10K2.u4138 = KTree.node A10K2.u4136 (nat_lit 67508272) (nat_lit 14614409437) (nat_lit 0) A10K2.u4137 from rfl, allE_node, arows4136, irow4138, arows4137]
  all_goals rfl

theorem atot4138 : totK PA10K2 A10K2.u4138 = [0, 1013481598833, 5182909483504, 8135792983722, 4232238871124, 676168114187, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4138 = KTree.node A10K2.u4136 (nat_lit 67508272) (nat_lit 14614409437) (nat_lit 0) A10K2.u4137 from rfl, totK_node, atot4136, atot4137]
  decide +kernel

theorem arows4143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4143 = true := by
  rw [show A10K2.u4143 = KTree.node A10K2.u4141 (nat_lit 67522611) (nat_lit 1380956301) (nat_lit 0) A10K2.u4142 from rfl, allE_node, arows4141, irow4143, arows4142]
  all_goals rfl

theorem atot4143 : totK PA10K2 A10K2.u4143 = [0, 788883354754, 4324677247227, 7781543452640, 4854279878678, 869903706797, 38021971230, 0, 0, 0] := by
  rw [show A10K2.u4143 = KTree.node A10K2.u4141 (nat_lit 67522611) (nat_lit 1380956301) (nat_lit 0) A10K2.u4142 from rfl, totK_node, atot4141, atot4142]
  decide +kernel

theorem arows4146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4146 = true := by
  rw [show A10K2.u4146 = KTree.node A10K2.u4144 (nat_lit 67552557) (nat_lit 6613700219) (nat_lit 0) A10K2.u4145 from rfl, allE_node, arows4144, irow4146, arows4145]
  all_goals rfl

theorem atot4146 : totK PA10K2 A10K2.u4146 = [0, 308867641608, 2189045408727, 6362359051374, 7173589505664, 2407346658643, 242085458233, 5676195732, 0, 0] := by
  rw [show A10K2.u4146 = KTree.node A10K2.u4144 (nat_lit 67552557) (nat_lit 6613700219) (nat_lit 0) A10K2.u4145 from rfl, totK_node, atot4144, atot4145]
  decide +kernel

theorem arows4150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4150 = true := by
  rw [show A10K2.u4150 = KTree.node A10K2.u4148 (nat_lit 67573804) (nat_lit 12647386733) (nat_lit 0) A10K2.u4149 from rfl, allE_node, arows4148, irow4150, arows4149]
  all_goals rfl

theorem atot4150 : totK PA10K2 A10K2.u4150 = [0, 1104492185663, 5434543401062, 8455009858170, 4261686846171, 621476586045, 25313348169, 0, 0, 0] := by
  rw [show A10K2.u4150 = KTree.node A10K2.u4148 (nat_lit 67573804) (nat_lit 12647386733) (nat_lit 0) A10K2.u4149 from rfl, totK_node, atot4148, atot4149]
  decide +kernel

theorem arows4153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4153 = true := by
  rw [show A10K2.u4153 = KTree.node A10K2.u4151 (nat_lit 67599438) (nat_lit 10943930858) (nat_lit 0) A10K2.u4152 from rfl, allE_node, arows4151, irow4153, arows4152]
  all_goals rfl

theorem atot4153 : totK PA10K2 A10K2.u4153 = [833436429740, 3197077393782, 5114456904586, 5668257605627, 3967689063956, 1026712828291, 62368562949, 0, 0, 0] := by
  rw [show A10K2.u4153 = KTree.node A10K2.u4151 (nat_lit 67599438) (nat_lit 10943930858) (nat_lit 0) A10K2.u4152 from rfl, totK_node, atot4151, atot4152]
  decide +kernel

theorem arows4160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4160 = true := by
  rw [show A10K2.u4160 = KTree.node A10K2.u4158 (nat_lit 68174272) (nat_lit 15258953680) (nat_lit 0) A10K2.u4159 from rfl, allE_node, arows4158, irow4160, arows4159]
  all_goals rfl

theorem atot4160 : totK PA10K2 A10K2.u4160 = [770023963405, 4593626299168, 8194763847740, 4693242293752, 745197846967, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4160 = KTree.node A10K2.u4158 (nat_lit 68174272) (nat_lit 15258953680) (nat_lit 0) A10K2.u4159 from rfl, totK_node, atot4158, atot4159]
  decide +kernel

theorem arows4163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4163 = true := by
  rw [show A10K2.u4163 = KTree.node A10K2.u4161 (nat_lit 68187030) (nat_lit 15303751834) (nat_lit 0) A10K2.u4162 from rfl, allE_node, arows4161, irow4163, arows4162]
  all_goals rfl

theorem atot4163 : totK PA10K2 A10K2.u4163 = [552312781151, 3516251937332, 7637866972832, 6162352909477, 1473114176147, 87127133923, 0, 0, 0, 0] := by
  rw [show A10K2.u4163 = KTree.node A10K2.u4161 (nat_lit 68187030) (nat_lit 15303751834) (nat_lit 0) A10K2.u4162 from rfl, totK_node, atot4161, atot4162]
  decide +kernel

theorem arows4167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4167 = true := by
  rw [show A10K2.u4167 = KTree.node A10K2.u4165 (nat_lit 68207159) (nat_lit 13165168703) (nat_lit 0) A10K2.u4166 from rfl, allE_node, arows4165, irow4167, arows4166]
  all_goals rfl

theorem atot4167 : totK PA10K2 A10K2.u4167 = [0, 768484807051, 4628705788435, 8249478129812, 4472635586165, 699865565596, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4167 = KTree.node A10K2.u4165 (nat_lit 68207159) (nat_lit 13165168703) (nat_lit 0) A10K2.u4166 from rfl, totK_node, atot4165, atot4166]
  decide +kernel

theorem arows4170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4170 = true := by
  rw [show A10K2.u4170 = KTree.node A10K2.u4168 (nat_lit 68233450) (nat_lit 12436460845) (nat_lit 0) A10K2.u4169 from rfl, allE_node, arows4168, irow4170, arows4169]
  all_goals rfl

theorem atot4170 : totK PA10K2 A10K2.u4170 = [762984113060, 4100036998502, 7504933988668, 5484461941230, 1551546122147, 176414017375, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4170 = KTree.node A10K2.u4168 (nat_lit 68233450) (nat_lit 12436460845) (nat_lit 0) A10K2.u4169 from rfl, totK_node, atot4168, atot4169]
  decide +kernel

theorem arows4175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4175 = true := by
  rw [show A10K2.u4175 = KTree.node A10K2.u4173 (nat_lit 68244771) (nat_lit 10289999058) (nat_lit 0) A10K2.u4174 from rfl, allE_node, arows4173, irow4175, arows4174]
  all_goals rfl

theorem atot4175 : totK PA10K2 A10K2.u4175 = [779393338859, 4370681245739, 8045360710426, 5181594118660, 967537167482, 38878015291, 0, 0, 0, 0] := by
  rw [show A10K2.u4175 = KTree.node A10K2.u4173 (nat_lit 68244771) (nat_lit 10289999058) (nat_lit 0) A10K2.u4174 from rfl, totK_node, atot4173, atot4174]
  decide +kernel

theorem arows4178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4178 = true := by
  rw [show A10K2.u4178 = KTree.node A10K2.u4176 (nat_lit 68273429) (nat_lit 6954779694) (nat_lit 0) A10K2.u4177 from rfl, allE_node, arows4176, irow4178, arows4177]
  all_goals rfl

theorem atot4178 : totK PA10K2 A10K2.u4178 = [0, 778975688571, 4498190685345, 8146795720116, 4782156247657, 823085542569, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4178 = KTree.node A10K2.u4176 (nat_lit 68273429) (nat_lit 6954779694) (nat_lit 0) A10K2.u4177 from rfl, totK_node, atot4176, atot4177]
  decide +kernel

theorem arows4182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4182 = true := by
  rw [show A10K2.u4182 = KTree.node A10K2.u4180 (nat_lit 68293234) (nat_lit 4530785029) (nat_lit 0) A10K2.u4181 from rfl, allE_node, arows4180, irow4182, arows4181]
  all_goals rfl

theorem atot4182 : totK PA10K2 A10K2.u4182 = [1389233555099, 5682879922327, 7679690351676, 3801820286544, 640269693955, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4182 = KTree.node A10K2.u4180 (nat_lit 68293234) (nat_lit 4530785029) (nat_lit 0) A10K2.u4181 from rfl, totK_node, atot4180, atot4181]
  decide +kernel

theorem arows4185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4185 = true := by
  rw [show A10K2.u4185 = KTree.node A10K2.u4183 (nat_lit 68306145) (nat_lit 4548598634) (nat_lit 0) A10K2.u4184 from rfl, allE_node, arows4183, irow4185, arows4184]
  all_goals rfl

theorem atot4185 : totK PA10K2 A10K2.u4185 = [864853315503, 4763962450765, 8122184332838, 4589684836698, 739879683485, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4185 = KTree.node A10K2.u4183 (nat_lit 68306145) (nat_lit 4548598634) (nat_lit 0) A10K2.u4184 from rfl, totK_node, atot4183, atot4184]
  decide +kernel

theorem arows4191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4191 = true := by
  rw [show A10K2.u4191 = KTree.node A10K2.u4189 (nat_lit 68331171) (nat_lit 10602907996) (nat_lit 0) A10K2.u4190 from rfl, allE_node, arows4189, irow4191, arows4190]
  all_goals rfl

theorem atot4191 : totK PA10K2 A10K2.u4191 = [0, 1939877889382, 7198129009973, 7732713121007, 2153955835911, 128845499320, 0, 0, 0, 0] := by
  rw [show A10K2.u4191 = KTree.node A10K2.u4189 (nat_lit 68331171) (nat_lit 10602907996) (nat_lit 0) A10K2.u4190 from rfl, totK_node, atot4189, atot4190]
  decide +kernel

theorem arows4194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4194 = true := by
  rw [show A10K2.u4194 = KTree.node A10K2.u4192 (nat_lit 68420051) (nat_lit 2018997646) (nat_lit 0) A10K2.u4193 from rfl, allE_node, arows4192, irow4194, arows4193]
  all_goals rfl

theorem atot4194 : totK PA10K2 A10K2.u4194 = [0, 1139903773436, 5328595887218, 7869303307213, 3855534202779, 654694165205, 31725663621, 0, 0, 0] := by
  rw [show A10K2.u4194 = KTree.node A10K2.u4192 (nat_lit 68420051) (nat_lit 2018997646) (nat_lit 0) A10K2.u4193 from rfl, totK_node, atot4192, atot4193]
  decide +kernel

theorem arows4198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4198 = true := by
  rw [show A10K2.u4198 = KTree.node A10K2.u4196 (nat_lit 68438273) (nat_lit 10098294115) (nat_lit 0) A10K2.u4197 from rfl, allE_node, arows4196, irow4198, arows4197]
  all_goals rfl

theorem atot4198 : totK PA10K2 A10K2.u4198 = [0, 1103840011156, 5197905025726, 8018683354907, 4122322029396, 568559332478, 11801668502, 0, 0, 0] := by
  rw [show A10K2.u4198 = KTree.node A10K2.u4196 (nat_lit 68438273) (nat_lit 10098294115) (nat_lit 0) A10K2.u4197 from rfl, totK_node, atot4196, atot4197]
  decide +kernel

theorem arows4201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4201 = true := by
  rw [show A10K2.u4201 = KTree.node A10K2.u4199 (nat_lit 68495394) (nat_lit 9239556487) (nat_lit 0) A10K2.u4200 from rfl, allE_node, arows4199, irow4201, arows4200]
  all_goals rfl

theorem atot4201 : totK PA10K2 A10K2.u4201 = [0, 980874430761, 4847763729538, 7975728690689, 4864476402494, 881726942482, 38305921858, 0, 0, 0] := by
  rw [show A10K2.u4201 = KTree.node A10K2.u4199 (nat_lit 68495394) (nat_lit 9239556487) (nat_lit 0) A10K2.u4200 from rfl, totK_node, atot4199, atot4200]
  decide +kernel

theorem arows4206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4206 = true := by
  rw [show A10K2.u4206 = KTree.node A10K2.u4204 (nat_lit 68506789) (nat_lit 7146558338) (nat_lit 0) A10K2.u4205 from rfl, allE_node, arows4204, irow4206, arows4205]
  all_goals rfl

theorem atot4206 : totK PA10K2 A10K2.u4206 = [0, 1462461220360, 5997456422880, 7933988262916, 3411024054439, 407728237650, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4206 = KTree.node A10K2.u4204 (nat_lit 68506789) (nat_lit 7146558338) (nat_lit 0) A10K2.u4205 from rfl, totK_node, atot4204, atot4205]
  decide +kernel

theorem arows4209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4209 = true := by
  rw [show A10K2.u4209 = KTree.node A10K2.u4207 (nat_lit 68560610) (nat_lit 13752822675) (nat_lit 0) A10K2.u4208 from rfl, allE_node, arows4207, irow4209, arows4208]
  all_goals rfl

theorem atot4209 : totK PA10K2 A10K2.u4209 = [0, 730491208058, 4300304618856, 7932746415794, 5019393675358, 953982064781, 61078328232, 0, 0, 0] := by
  rw [show A10K2.u4209 = KTree.node A10K2.u4207 (nat_lit 68560610) (nat_lit 13752822675) (nat_lit 0) A10K2.u4208 from rfl, totK_node, atot4207, atot4208]
  decide +kernel

theorem arows4213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4213 = true := by
  rw [show A10K2.u4213 = KTree.node A10K2.u4211 (nat_lit 68571584) (nat_lit 14830998214) (nat_lit 0) A10K2.u4212 from rfl, allE_node, arows4211, irow4213, arows4212]
  all_goals rfl

theorem atot4213 : totK PA10K2 A10K2.u4213 = [0, 835897603759, 4464929480289, 7818203632871, 4727561494288, 847386528928, 37547833973, 0, 0, 0] := by
  rw [show A10K2.u4213 = KTree.node A10K2.u4211 (nat_lit 68571584) (nat_lit 14830998214) (nat_lit 0) A10K2.u4212 from rfl, totK_node, atot4211, atot4212]
  decide +kernel

theorem arows4216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4216 = true := by
  rw [show A10K2.u4216 = KTree.node A10K2.u4214 (nat_lit 68601054) (nat_lit 9403890332) (nat_lit 0) A10K2.u4215 from rfl, allE_node, arows4214, irow4216, arows4215]
  all_goals rfl

theorem atot4216 : totK PA10K2 A10K2.u4216 = [0, 0, 1612365030528, 6448336496699, 7537826308883, 2666286938420, 255874176371, 0, 0, 0] := by
  rw [show A10K2.u4216 = KTree.node A10K2.u4214 (nat_lit 68601054) (nat_lit 9403890332) (nat_lit 0) A10K2.u4215 from rfl, totK_node, atot4214, atot4215]
  decide +kernel

theorem arows4224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4224 = true := by
  rw [show A10K2.u4224 = KTree.node A10K2.u4222 (nat_lit 68686208) (nat_lit 15445956646) (nat_lit 0) A10K2.u4223 from rfl, allE_node, arows4222, irow4224, arows4223]
  all_goals rfl

theorem atot4224 : totK PA10K2 A10K2.u4224 = [1402530133197, 5549850691842, 7613583839494, 3931924833774, 662357577859, 124671762955, 84918787380, 6354482628, 0, 0] := by
  rw [show A10K2.u4224 = KTree.node A10K2.u4222 (nat_lit 68686208) (nat_lit 15445956646) (nat_lit 0) A10K2.u4223 from rfl, totK_node, atot4222, atot4223]
  decide +kernel

theorem arows4227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4227 = true := by
  rw [show A10K2.u4227 = KTree.node A10K2.u4225 (nat_lit 68708273) (nat_lit 7628858159) (nat_lit 0) A10K2.u4226 from rfl, allE_node, arows4225, irow4227, arows4226]
  all_goals rfl

theorem atot4227 : totK PA10K2 A10K2.u4227 = [802911436883, 4706461549558, 8420324755602, 5159981341001, 872359447655, 20168938236, 0, 0, 0, 0] := by
  rw [show A10K2.u4227 = KTree.node A10K2.u4225 (nat_lit 68708273) (nat_lit 7628858159) (nat_lit 0) A10K2.u4226 from rfl, totK_node, atot4225, atot4226]
  decide +kernel

theorem arows4231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4231 = true := by
  rw [show A10K2.u4231 = KTree.node A10K2.u4229 (nat_lit 68718636) (nat_lit 12040938746) (nat_lit 0) A10K2.u4230 from rfl, allE_node, arows4229, irow4231, arows4230]
  all_goals rfl

theorem atot4231 : totK PA10K2 A10K2.u4231 = [0, 1260806690304, 5464634372251, 7836279680138, 3942345662924, 655502482048, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4231 = KTree.node A10K2.u4229 (nat_lit 68718636) (nat_lit 12040938746) (nat_lit 0) A10K2.u4230 from rfl, totK_node, atot4229, atot4230]
  decide +kernel

theorem arows4234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4234 = true := by
  rw [show A10K2.u4234 = KTree.node A10K2.u4232 (nat_lit 68740823) (nat_lit 10130369093) (nat_lit 0) A10K2.u4233 from rfl, allE_node, arows4232, irow4234, arows4233]
  all_goals rfl

theorem atot4234 : totK PA10K2 A10K2.u4234 = [780629253406, 3415708893992, 6396840389337, 6260163236011, 2474682471825, 270542952500, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4234 = KTree.node A10K2.u4232 (nat_lit 68740823) (nat_lit 10130369093) (nat_lit 0) A10K2.u4233 from rfl, totK_node, atot4232, atot4233]
  decide +kernel

theorem arows4239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4239 = true := by
  rw [show A10K2.u4239 = KTree.node A10K2.u4237 (nat_lit 68888248) (nat_lit 9353580640) (nat_lit 0) A10K2.u4238 from rfl, allE_node, arows4237, irow4239, arows4238]
  all_goals rfl

theorem atot4239 : totK PA10K2 A10K2.u4239 = [877440351564, 4575922592349, 8157790862117, 5312366105851, 1041623362216, 56329937382, 0, 0, 0, 0] := by
  rw [show A10K2.u4239 = KTree.node A10K2.u4237 (nat_lit 68888248) (nat_lit 9353580640) (nat_lit 0) A10K2.u4238 from rfl, totK_node, atot4237, atot4238]
  decide +kernel

theorem arows4242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4242 = true := by
  rw [show A10K2.u4242 = KTree.node A10K2.u4240 (nat_lit 68907905) (nat_lit 10268712696) (nat_lit 0) A10K2.u4241 from rfl, allE_node, arows4240, irow4242, arows4241]
  all_goals rfl

theorem atot4242 : totK PA10K2 A10K2.u4242 = [585790443428, 3874396752566, 7943690354940, 5969675012536, 1484144591686, 88459438038, 0, 0, 0, 0] := by
  rw [show A10K2.u4242 = KTree.node A10K2.u4240 (nat_lit 68907905) (nat_lit 10268712696) (nat_lit 0) A10K2.u4241 from rfl, totK_node, atot4240, atot4241]
  decide +kernel

theorem arows4246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4246 = true := by
  rw [show A10K2.u4246 = KTree.node A10K2.u4244 (nat_lit 68920561) (nat_lit 4836326203) (nat_lit 0) A10K2.u4245 from rfl, allE_node, arows4244, irow4246, arows4245]
  all_goals rfl

theorem atot4246 : totK PA10K2 A10K2.u4246 = [0, 967199386544, 5016299434891, 8471642255153, 4833184365340, 694996855911, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u4246 = KTree.node A10K2.u4244 (nat_lit 68920561) (nat_lit 4836326203) (nat_lit 0) A10K2.u4245 from rfl, totK_node, atot4244, atot4245]
  decide +kernel

theorem arows4249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4249 = true := by
  rw [show A10K2.u4249 = KTree.node A10K2.u4247 (nat_lit 68940247) (nat_lit 14298747187) (nat_lit 0) A10K2.u4248 from rfl, allE_node, arows4247, irow4249, arows4248]
  all_goals rfl

theorem atot4249 : totK PA10K2 A10K2.u4249 = [0, 1114444962745, 5037150098381, 7781351684615, 4780295429511, 1018470278411, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u4249 = KTree.node A10K2.u4247 (nat_lit 68940247) (nat_lit 14298747187) (nat_lit 0) A10K2.u4248 from rfl, totK_node, atot4247, atot4248]
  decide +kernel

theorem arows4255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4255 = true := by
  rw [show A10K2.u4255 = KTree.node A10K2.u4253 (nat_lit 68950529) (nat_lit 10478560941) (nat_lit 0) A10K2.u4254 from rfl, allE_node, arows4253, irow4255, arows4254]
  all_goals rfl

theorem atot4255 : totK PA10K2 A10K2.u4255 = [0, 1087194705325, 5218910755742, 8039892507266, 4195442605877, 685612865471, 30780440178, 0, 0, 0] := by
  rw [show A10K2.u4255 = KTree.node A10K2.u4253 (nat_lit 68950529) (nat_lit 10478560941) (nat_lit 0) A10K2.u4254 from rfl, totK_node, atot4253, atot4254]
  decide +kernel

theorem arows4258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4258 = true := by
  rw [show A10K2.u4258 = KTree.node A10K2.u4256 (nat_lit 68972531) (nat_lit 8194827383) (nat_lit 0) A10K2.u4257 from rfl, allE_node, arows4256, irow4258, arows4257]
  all_goals rfl

theorem atot4258 : totK PA10K2 A10K2.u4258 = [0, 802911436883, 4231640121772, 7909189110580, 5720747778308, 1279198092062, 68056836726, 0, 0, 0] := by
  rw [show A10K2.u4258 = KTree.node A10K2.u4256 (nat_lit 68972531) (nat_lit 8194827383) (nat_lit 0) A10K2.u4257 from rfl, totK_node, atot4256, atot4257]
  decide +kernel

theorem arows4262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4262 = true := by
  rw [show A10K2.u4262 = KTree.node A10K2.u4260 (nat_lit 68983080) (nat_lit 12077524836) (nat_lit 0) A10K2.u4261 from rfl, allE_node, arows4260, irow4262, arows4261]
  all_goals rfl

theorem atot4262 : totK PA10K2 A10K2.u4262 = [0, 0, 1522727651060, 6328585131048, 7966222946443, 3057068850747, 351804165928, 7007974415, 0, 0] := by
  rw [show A10K2.u4262 = KTree.node A10K2.u4260 (nat_lit 68983080) (nat_lit 12077524836) (nat_lit 0) A10K2.u4261 from rfl, totK_node, atot4260, atot4261]
  decide +kernel

theorem arows4265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4265 = true := by
  rw [show A10K2.u4265 = KTree.node A10K2.u4263 (nat_lit 69143773) (nat_lit 1739775499) (nat_lit 0) A10K2.u4264 from rfl, allE_node, arows4263, irow4265, arows4264]
  all_goals rfl

theorem atot4265 : totK PA10K2 A10K2.u4265 = [0, 1068376898294, 4762956205697, 7634747307608, 5142334476750, 1224822185043, 68812355783, 0, 0, 0] := by
  rw [show A10K2.u4265 = KTree.node A10K2.u4263 (nat_lit 69143773) (nat_lit 1739775499) (nat_lit 0) A10K2.u4264 from rfl, totK_node, atot4263, atot4264]
  decide +kernel

theorem arows4270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4270 = true := by
  rw [show A10K2.u4270 = KTree.node A10K2.u4268 (nat_lit 69165452) (nat_lit 8125911805) (nat_lit 0) A10K2.u4269 from rfl, allE_node, arows4268, irow4270, arows4269]
  all_goals rfl

theorem atot4270 : totK PA10K2 A10K2.u4270 = [0, 1173992882942, 5480767499833, 8306602215642, 4441121822908, 694674391712, 18992036149, 0, 0, 0] := by
  rw [show A10K2.u4270 = KTree.node A10K2.u4268 (nat_lit 69165452) (nat_lit 8125911805) (nat_lit 0) A10K2.u4269 from rfl, totK_node, atot4268, atot4269]
  decide +kernel

theorem arows4273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4273 = true := by
  rw [show A10K2.u4273 = KTree.node A10K2.u4271 (nat_lit 69175594) (nat_lit 8117000439) (nat_lit 0) A10K2.u4272 from rfl, allE_node, arows4271, irow4273, arows4272]
  all_goals rfl

theorem atot4273 : totK PA10K2 A10K2.u4273 = [0, 0, 1647399859362, 6488311313841, 8105834940576, 3238585534050, 340704616251, 6318667960, 0, 0] := by
  rw [show A10K2.u4273 = KTree.node A10K2.u4271 (nat_lit 69175594) (nat_lit 8117000439) (nat_lit 0) A10K2.u4272 from rfl, totK_node, atot4271, atot4272]
  decide +kernel

theorem arows4277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4277 = true := by
  rw [show A10K2.u4277 = KTree.node A10K2.u4275 (nat_lit 69198256) (nat_lit 14624731837) (nat_lit 0) A10K2.u4276 from rfl, allE_node, arows4275, irow4277, arows4276]
  all_goals rfl

theorem atot4277 : totK PA10K2 A10K2.u4277 = [0, 0, 1167610775119, 5514870698817, 8380903354126, 4219539517197, 519782902459, 12460675034, 0, 0] := by
  rw [show A10K2.u4277 = KTree.node A10K2.u4275 (nat_lit 69198256) (nat_lit 14624731837) (nat_lit 0) A10K2.u4276 from rfl, totK_node, atot4275, atot4276]
  decide +kernel

theorem arows4280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4280 = true := by
  rw [show A10K2.u4280 = KTree.node A10K2.u4278 (nat_lit 69208288) (nat_lit 9009101019) (nat_lit 0) A10K2.u4279 from rfl, allE_node, arows4278, irow4280, arows4279]
  all_goals rfl

theorem atot4280 : totK PA10K2 A10K2.u4280 = [0, 869022221310, 3752520685516, 6060044947274, 5020099035296, 2843811663151, 778263642059, 54997142734, 0, 0] := by
  rw [show A10K2.u4280 = KTree.node A10K2.u4278 (nat_lit 69208288) (nat_lit 9009101019) (nat_lit 0) A10K2.u4279 from rfl, totK_node, atot4278, atot4279]
  decide +kernel

theorem arows4287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4287 = true := by
  rw [show A10K2.u4287 = KTree.node A10K2.u4285 (nat_lit 69226752) (nat_lit 14814158032) (nat_lit 0) A10K2.u4286 from rfl, allE_node, arows4285, irow4287, arows4286]
  all_goals rfl

theorem atot4287 : totK PA10K2 A10K2.u4287 = [0, 1420102134627, 5862516475541, 7758301102627, 3453718246987, 431738034561, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u4287 = KTree.node A10K2.u4285 (nat_lit 69226752) (nat_lit 14814158032) (nat_lit 0) A10K2.u4286 from rfl, totK_node, atot4285, atot4286]
  decide +kernel

theorem arows4290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4290 = true := by
  rw [show A10K2.u4290 = KTree.node A10K2.u4288 (nat_lit 69238881) (nat_lit 10022573639) (nat_lit 0) A10K2.u4289 from rfl, allE_node, arows4288, irow4290, arows4289]
  all_goals rfl

theorem atot4290 : totK PA10K2 A10K2.u4290 = [0, 31409270183, 2099845988183, 7177323856673, 7629111542537, 2418239697854, 177136671928, 0, 0, 0] := by
  rw [show A10K2.u4290 = KTree.node A10K2.u4288 (nat_lit 69238881) (nat_lit 10022573639) (nat_lit 0) A10K2.u4289 from rfl, totK_node, atot4288, atot4289]
  decide +kernel

theorem arows4294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4294 = true := by
  rw [show A10K2.u4294 = KTree.node A10K2.u4292 (nat_lit 69257376) (nat_lit 8996602234) (nat_lit 0) A10K2.u4293 from rfl, allE_node, arows4292, irow4294, arows4293]
  all_goals rfl

theorem atot4294 : totK PA10K2 A10K2.u4294 = [0, 0, 1159775356246, 5195111754736, 7636409799015, 3852349453456, 701695676978, 36196801203, 0, 0] := by
  rw [show A10K2.u4294 = KTree.node A10K2.u4292 (nat_lit 69257376) (nat_lit 8996602234) (nat_lit 0) A10K2.u4293 from rfl, totK_node, atot4292, atot4293]
  decide +kernel

theorem arows4297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4297 = true := by
  rw [show A10K2.u4297 = KTree.node A10K2.u4295 (nat_lit 69340174) (nat_lit 14493197135) (nat_lit 0) A10K2.u4296 from rfl, allE_node, arows4295, irow4297, arows4296]
  all_goals rfl

theorem atot4297 : totK PA10K2 A10K2.u4297 = [0, 998092700503, 4533890775720, 7479491922267, 5125976198657, 1245493261283, 72568879192, 0, 0, 0] := by
  rw [show A10K2.u4297 = KTree.node A10K2.u4295 (nat_lit 69340174) (nat_lit 14493197135) (nat_lit 0) A10K2.u4296 from rfl, totK_node, atot4295, atot4296]
  decide +kernel

theorem arows4302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4302 = true := by
  rw [show A10K2.u4302 = KTree.node A10K2.u4300 (nat_lit 69354682) (nat_lit 13642327321) (nat_lit 0) A10K2.u4301 from rfl, allE_node, arows4300, irow4302, arows4301]
  all_goals rfl

theorem atot4302 : totK PA10K2 A10K2.u4302 = [0, 1056485411382, 5279866529722, 8126982355617, 3805117010336, 428886374705, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4302 = KTree.node A10K2.u4300 (nat_lit 69354682) (nat_lit 13642327321) (nat_lit 0) A10K2.u4301 from rfl, totK_node, atot4300, atot4301]
  decide +kernel

theorem arows4305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4305 = true := by
  rw [show A10K2.u4305 = KTree.node A10K2.u4303 (nat_lit 69380105) (nat_lit 8740942217) (nat_lit 0) A10K2.u4304 from rfl, allE_node, arows4303, irow4305, arows4304]
  all_goals rfl

theorem atot4305 : totK PA10K2 A10K2.u4305 = [0, 0, 2045305021618, 7459180564306, 7597888210863, 1821063071241, 87656715200, 0, 0, 0] := by
  rw [show A10K2.u4305 = KTree.node A10K2.u4303 (nat_lit 69380105) (nat_lit 8740942217) (nat_lit 0) A10K2.u4304 from rfl, totK_node, atot4303, atot4304]
  decide +kernel

theorem arows4309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4309 = true := by
  rw [show A10K2.u4309 = KTree.node A10K2.u4307 (nat_lit 69405736) (nat_lit 12602377378) (nat_lit 0) A10K2.u4308 from rfl, allE_node, arows4307, irow4309, arows4308]
  all_goals rfl

theorem atot4309 : totK PA10K2 A10K2.u4309 = [0, 890310851288, 3941164519932, 6747555037194, 5517731414450, 1918236676944, 224345500730, 5976421810, 0, 0] := by
  rw [show A10K2.u4309 = KTree.node A10K2.u4307 (nat_lit 69405736) (nat_lit 12602377378) (nat_lit 0) A10K2.u4308 from rfl, totK_node, atot4307, atot4308]
  decide +kernel

theorem arows4312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4312 = true := by
  rw [show A10K2.u4312 = KTree.node A10K2.u4310 (nat_lit 69430660) (nat_lit 7298657798) (nat_lit 0) A10K2.u4311 from rfl, allE_node, arows4310, irow4312, arows4311]
  all_goals rfl

theorem atot4312 : totK PA10K2 A10K2.u4312 = [0, 997145218375, 4871389744792, 8136912257677, 5255683979247, 1026305176855, 25401055518, 0, 0, 0] := by
  rw [show A10K2.u4312 = KTree.node A10K2.u4310 (nat_lit 69430660) (nat_lit 7298657798) (nat_lit 0) A10K2.u4311 from rfl, totK_node, atot4310, atot4311]
  decide +kernel

theorem arows4318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4318 = true := by
  rw [show A10K2.u4318 = KTree.node A10K2.u4316 (nat_lit 69439945) (nat_lit 6837354806) (nat_lit 0) A10K2.u4317 from rfl, allE_node, arows4316, irow4318, arows4317]
  all_goals rfl

theorem atot4318 : totK PA10K2 A10K2.u4318 = [0, 0, 1457386960436, 6017813529386, 8123444372521, 3743145088511, 443081166892, 6904928264, 0, 0] := by
  rw [show A10K2.u4318 = KTree.node A10K2.u4316 (nat_lit 69439945) (nat_lit 6837354806) (nat_lit 0) A10K2.u4317 from rfl, totK_node, atot4316, atot4317]
  decide +kernel

theorem arows4321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4321 = true := by
  rw [show A10K2.u4321 = KTree.node A10K2.u4319 (nat_lit 69467642) (nat_lit 13143785444) (nat_lit 0) A10K2.u4320 from rfl, allE_node, arows4319, irow4321, arows4320]
  all_goals rfl

theorem atot4321 : totK PA10K2 A10K2.u4321 = [0, 0, 1292275731208, 5627190600444, 7942744953425, 4092900605640, 702377739897, 34570548376, 0, 0] := by
  rw [show A10K2.u4321 = KTree.node A10K2.u4319 (nat_lit 69467642) (nat_lit 13143785444) (nat_lit 0) A10K2.u4320 from rfl, totK_node, atot4319, atot4320]
  decide +kernel

theorem arows4325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4325 = true := by
  rw [show A10K2.u4325 = KTree.node A10K2.u4323 (nat_lit 69485491) (nat_lit 4294822496) (nat_lit 0) A10K2.u4324 from rfl, allE_node, arows4323, irow4325, arows4324]
  all_goals rfl

theorem atot4325 : totK PA10K2 A10K2.u4325 = [0, 0, 875902367471, 4536181845225, 7797465112878, 4493771406310, 799810183068, 36536693801, 0, 0] := by
  rw [show A10K2.u4325 = KTree.node A10K2.u4323 (nat_lit 69485491) (nat_lit 4294822496) (nat_lit 0) A10K2.u4324 from rfl, totK_node, atot4323, atot4324]
  decide +kernel

theorem arows4328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4328 = true := by
  rw [show A10K2.u4328 = KTree.node A10K2.u4326 (nat_lit 69499910) (nat_lit 15385015361) (nat_lit 0) A10K2.u4327 from rfl, allE_node, arows4326, irow4328, arows4327]
  all_goals rfl

theorem atot4328 : totK PA10K2 A10K2.u4328 = [0, 0, 586772247909, 3905392282970, 8015047996921, 5724733512872, 1206464542216, 66253585394, 0, 0] := by
  rw [show A10K2.u4328 = KTree.node A10K2.u4326 (nat_lit 69499910) (nat_lit 15385015361) (nat_lit 0) A10K2.u4327 from rfl, totK_node, atot4326, atot4327]
  decide +kernel

theorem arows4333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4333 = true := by
  rw [show A10K2.u4333 = KTree.node A10K2.u4331 (nat_lit 69517921) (nat_lit 9855019759) (nat_lit 0) A10K2.u4332 from rfl, allE_node, arows4331, irow4333, arows4332]
  all_goals rfl

theorem atot4333 : totK PA10K2 A10K2.u4333 = [0, 0, 0, 829420916833, 4521293082587, 7637341416207, 4306369160150, 769383815391, 36134558889, 0] := by
  rw [show A10K2.u4333 = KTree.node A10K2.u4331 (nat_lit 69517921) (nat_lit 9855019759) (nat_lit 0) A10K2.u4332 from rfl, totK_node, atot4331, atot4332]
  decide +kernel

theorem arows4336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4336 = true := by
  rw [show A10K2.u4336 = KTree.node A10K2.u4334 (nat_lit 69601548) (nat_lit 12085458580) (nat_lit 0) A10K2.u4335 from rfl, allE_node, arows4334, irow4336, arows4335]
  all_goals rfl

theorem atot4336 : totK PA10K2 A10K2.u4336 = [0, 0, 792926426390, 4268764452117, 7822982459328, 5247270842255, 1161858133362, 69226305622, 0, 0] := by
  rw [show A10K2.u4336 = KTree.node A10K2.u4334 (nat_lit 69601548) (nat_lit 12085458580) (nat_lit 0) A10K2.u4335 from rfl, totK_node, atot4334, atot4335]
  decide +kernel

theorem arows4340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4340 = true := by
  rw [show A10K2.u4340 = KTree.node A10K2.u4338 (nat_lit 69616385) (nat_lit 10313198917) (nat_lit 0) A10K2.u4339 from rfl, allE_node, arows4338, irow4340, arows4339]
  all_goals rfl

theorem atot4340 : totK PA10K2 A10K2.u4340 = [0, 0, 1256336767976, 5796786754417, 8134347356044, 3172115516120, 270069197365, 5656154743, 0, 0] := by
  rw [show A10K2.u4340 = KTree.node A10K2.u4338 (nat_lit 69616385) (nat_lit 10313198917) (nat_lit 0) A10K2.u4339 from rfl, totK_node, atot4338, atot4339]
  decide +kernel

theorem arows4343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4343 = true := by
  rw [show A10K2.u4343 = KTree.node A10K2.u4341 (nat_lit 69642337) (nat_lit 9350552202) (nat_lit 0) A10K2.u4342 from rfl, allE_node, arows4341, irow4343, arows4342]
  all_goals rfl

theorem atot4343 : totK PA10K2 A10K2.u4343 = [0, 0, 0, 2033639210443, 7484550072254, 7244733689225, 1697192988686, 101460081958, 0, 0] := by
  rw [show A10K2.u4343 = KTree.node A10K2.u4341 (nat_lit 69642337) (nat_lit 9350552202) (nat_lit 0) A10K2.u4342 from rfl, totK_node, atot4341, atot4342]
  decide +kernel

theorem arows4352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4352 = true := by
  rw [show A10K2.u4352 = KTree.node A10K2.u4350 (nat_lit 69668062) (nat_lit 11413841752) (nat_lit 0) A10K2.u4351 from rfl, allE_node, arows4350, irow4352, arows4351]
  all_goals rfl

theorem atot4352 : totK PA10K2 A10K2.u4352 = [0, 0, 1085898326061, 4660577270544, 7153176783542, 4764910777958, 1481193325112, 191793247277, 5676195732, 0] := by
  rw [show A10K2.u4352 = KTree.node A10K2.u4350 (nat_lit 69668062) (nat_lit 11413841752) (nat_lit 0) A10K2.u4351 from rfl, totK_node, atot4350, atot4351]
  decide +kernel

theorem arows4355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4355 = true := by
  rw [show A10K2.u4355 = KTree.node A10K2.u4353 (nat_lit 69693854) (nat_lit 15438541665) (nat_lit 0) A10K2.u4354 from rfl, allE_node, arows4353, irow4355, arows4354]
  all_goals rfl

theorem atot4355 : totK PA10K2 A10K2.u4355 = [0, 583356039855, 2731948778882, 5606838301532, 6652824366265, 3673867503503, 699173414626, 35503361870, 0, 0] := by
  rw [show A10K2.u4355 = KTree.node A10K2.u4353 (nat_lit 69693854) (nat_lit 15438541665) (nat_lit 0) A10K2.u4354 from rfl, totK_node, atot4353, atot4354]
  decide +kernel

theorem arows4359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4359 = true := by
  rw [show A10K2.u4359 = KTree.node A10K2.u4357 (nat_lit 70262152) (nat_lit 14054059202) (nat_lit 0) A10K2.u4358 from rfl, allE_node, arows4357, irow4359, arows4358]
  all_goals rfl

theorem atot4359 : totK PA10K2 A10K2.u4359 = [0, 1018881494712, 5049496776903, 7976265293153, 4293622995887, 682838079036, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4359 = KTree.node A10K2.u4357 (nat_lit 70262152) (nat_lit 14054059202) (nat_lit 0) A10K2.u4358 from rfl, totK_node, atot4357, atot4358]
  decide +kernel

theorem arows4362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4362 = true := by
  rw [show A10K2.u4362 = KTree.node A10K2.u4360 (nat_lit 70283524) (nat_lit 12531765557) (nat_lit 0) A10K2.u4361 from rfl, allE_node, arows4360, irow4362, arows4361]
  all_goals rfl

theorem atot4362 : totK PA10K2 A10K2.u4362 = [0, 552312781151, 3596041046801, 7839482041774, 6044970555437, 1343097277788, 67524920334, 0, 0, 0] := by
  rw [show A10K2.u4362 = KTree.node A10K2.u4360 (nat_lit 70283524) (nat_lit 12531765557) (nat_lit 0) A10K2.u4361 from rfl, totK_node, atot4360, atot4361]
  decide +kernel

theorem arows4367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4367 = true := by
  rw [show A10K2.u4367 = KTree.node A10K2.u4365 (nat_lit 70303788) (nat_lit 12812578913) (nat_lit 0) A10K2.u4366 from rfl, allE_node, arows4365, irow4367, arows4366]
  all_goals rfl

theorem atot4367 : totK PA10K2 A10K2.u4367 = [0, 0, 1016918753389, 5118117772939, 8044865342796, 4011559709129, 646790806661, 30650496230, 0, 0] := by
  rw [show A10K2.u4367 = KTree.node A10K2.u4365 (nat_lit 70303788) (nat_lit 12812578913) (nat_lit 0) A10K2.u4366 from rfl, totK_node, atot4365, atot4366]
  decide +kernel

theorem arows4370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4370 = true := by
  rw [show A10K2.u4370 = KTree.node A10K2.u4368 (nat_lit 70330139) (nat_lit 9981964682) (nat_lit 0) A10K2.u4369 from rfl, allE_node, arows4368, irow4370, arows4369]
  all_goals rfl

theorem atot4370 : totK PA10K2 A10K2.u4370 = [0, 762984113060, 3910780411367, 7132496491518, 5599056803212, 1854447250377, 214881011755, 5546304973, 0, 0] := by
  rw [show A10K2.u4370 = KTree.node A10K2.u4368 (nat_lit 70330139) (nat_lit 9981964682) (nat_lit 0) A10K2.u4369 from rfl, totK_node, atot4368, atot4369]
  decide +kernel

theorem arows4374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4374 = true := by
  rw [show A10K2.u4374 = KTree.node A10K2.u4372 (nat_lit 70340709) (nat_lit 7000149661) (nat_lit 0) A10K2.u4373 from rfl, allE_node, arows4372, irow4374, arows4373]
  all_goals rfl

theorem atot4374 : totK PA10K2 A10K2.u4374 = [0, 778819795920, 4366021486507, 8017162999719, 5126124444399, 940041803837, 38650245000, 0, 0, 0] := by
  rw [show A10K2.u4374 = KTree.node A10K2.u4372 (nat_lit 70340709) (nat_lit 7000149661) (nat_lit 0) A10K2.u4373 from rfl, totK_node, atot4372, atot4373]
  decide +kernel

theorem arows4377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4377 = true := by
  rw [show A10K2.u4377 = KTree.node A10K2.u4375 (nat_lit 70373480) (nat_lit 9935045620) (nat_lit 0) A10K2.u4376 from rfl, allE_node, arows4375, irow4377, arows4376]
  all_goals rfl

theorem atot4377 : totK PA10K2 A10K2.u4377 = [0, 579756899725, 3072761866552, 6398584924431, 6444840636923, 2374181881252, 256576575526, 6121173289, 0, 0] := by
  rw [show A10K2.u4377 = KTree.node A10K2.u4375 (nat_lit 70373480) (nat_lit 9935045620) (nat_lit 0) A10K2.u4376 from rfl, totK_node, atot4375, atot4376]
  decide +kernel

theorem arows4383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4383 = true := by
  rw [show A10K2.u4383 = KTree.node A10K2.u4381 (nat_lit 70395315) (nat_lit 9912139066) (nat_lit 0) A10K2.u4382 from rfl, allE_node, arows4381, irow4383, arows4382]
  all_goals rfl

theorem atot4383 : totK PA10K2 A10K2.u4383 = [0, 834992236178, 4359586656356, 7883472398585, 5120055420725, 971300260701, 56131144985, 0, 0, 0] := by
  rw [show A10K2.u4383 = KTree.node A10K2.u4381 (nat_lit 70395315) (nat_lit 9912139066) (nat_lit 0) A10K2.u4382 from rfl, totK_node, atot4381, atot4382]
  decide +kernel

theorem arows4386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4386 = true := by
  rw [show A10K2.u4386 = KTree.node A10K2.u4384 (nat_lit 70406250) (nat_lit 4878918850) (nat_lit 0) A10K2.u4385 from rfl, allE_node, arows4384, irow4386, arows4385]
  all_goals rfl

theorem atot4386 : totK PA10K2 A10K2.u4386 = [0, 836900465410, 4545017667484, 7906041065981, 4777049041199, 866237557549, 38021971230, 0, 0, 0] := by
  rw [show A10K2.u4386 = KTree.node A10K2.u4384 (nat_lit 70406250) (nat_lit 4878918850) (nat_lit 0) A10K2.u4385 from rfl, totK_node, atot4384, atot4385]
  decide +kernel

theorem arows4390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4390 = true := by
  rw [show A10K2.u4390 = KTree.node A10K2.u4388 (nat_lit 70435200) (nat_lit 15058423936) (nat_lit 0) A10K2.u4389 from rfl, allE_node, arows4388, irow4390, arows4389]
  all_goals rfl

theorem atot4390 : totK PA10K2 A10K2.u4390 = [0, 0, 1664148271284, 6851384400717, 8020049963490, 2328091412117, 153956734571, 0, 0, 0] := by
  rw [show A10K2.u4390 = KTree.node A10K2.u4388 (nat_lit 70435200) (nat_lit 15058423936) (nat_lit 0) A10K2.u4389 from rfl, totK_node, atot4388, atot4389]
  decide +kernel

theorem arows4393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4393 = true := by
  rw [show A10K2.u4393 = KTree.node A10K2.u4391 (nat_lit 70520393) (nat_lit 6795308320) (nat_lit 0) A10K2.u4392 from rfl, allE_node, arows4391, irow4393, arows4392]
  all_goals rfl

theorem atot4393 : totK PA10K2 A10K2.u4393 = [0, 0, 1119547209295, 4929671881943, 7640314877467, 4319633771545, 822444124695, 37172849495, 0, 0] := by
  rw [show A10K2.u4393 = KTree.node A10K2.u4391 (nat_lit 70520393) (nat_lit 6795308320) (nat_lit 0) A10K2.u4392 from rfl, totK_node, atot4391, atot4392]
  decide +kernel

theorem arows4398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4398 = true := by
  rw [show A10K2.u4398 = KTree.node A10K2.u4396 (nat_lit 70540039) (nat_lit 4762421501) (nat_lit 0) A10K2.u4397 from rfl, allE_node, arows4396, irow4398, arows4397]
  all_goals rfl

theorem atot4398 : totK PA10K2 A10K2.u4398 = [0, 0, 1030483407750, 5220301003398, 8282187136926, 4122741279796, 537903130640, 13207830636, 0, 0] := by
  rw [show A10K2.u4398 = KTree.node A10K2.u4396 (nat_lit 70540039) (nat_lit 4762421501) (nat_lit 0) A10K2.u4397 from rfl, totK_node, atot4396, atot4397]
  decide +kernel

theorem arows4401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4401 = true := by
  rw [show A10K2.u4401 = KTree.node A10K2.u4399 (nat_lit 70599895) (nat_lit 12041950585) (nat_lit 0) A10K2.u4400 from rfl, allE_node, arows4399, irow4401, arows4400]
  all_goals rfl

theorem atot4401 : totK PA10K2 A10K2.u4401 = [0, 0, 1523228773836, 6367710319908, 8115594753634, 2986809714844, 228833101590, 0, 0, 0] := by
  rw [show A10K2.u4401 = KTree.node A10K2.u4399 (nat_lit 70599895) (nat_lit 12041950585) (nat_lit 0) A10K2.u4400 from rfl, totK_node, atot4399, atot4400]
  decide +kernel

theorem arows4405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4405 = true := by
  rw [show A10K2.u4405 = KTree.node A10K2.u4403 (nat_lit 70652529) (nat_lit 7222134195) (nat_lit 0) A10K2.u4404 from rfl, allE_node, arows4403, irow4405, arows4404]
  all_goals rfl

theorem atot4405 : totK PA10K2 A10K2.u4405 = [0, 0, 1412628620724, 5744708600947, 7600801446831, 3582410110654, 612303785358, 36429366174, 0, 0] := by
  rw [show A10K2.u4405 = KTree.node A10K2.u4403 (nat_lit 70652529) (nat_lit 7222134195) (nat_lit 0) A10K2.u4404 from rfl, totK_node, atot4403, atot4404]
  decide +kernel

theorem arows4408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4408 = true := by
  rw [show A10K2.u4408 = KTree.node A10K2.u4406 (nat_lit 70666297) (nat_lit 6872498827) (nat_lit 0) A10K2.u4407 from rfl, allE_node, arows4406, irow4408, arows4407]
  all_goals rfl

theorem atot4408 : totK PA10K2 A10K2.u4408 = [0, 0, 833271881333, 4836317071323, 8268021002469, 4200844528805, 576566772181, 12388698189, 0, 0] := by
  rw [show A10K2.u4408 = KTree.node A10K2.u4406 (nat_lit 70666297) (nat_lit 6872498827) (nat_lit 0) A10K2.u4407 from rfl, totK_node, atot4406, atot4407]
  decide +kernel

theorem arows4415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4415 = true := by
  rw [show A10K2.u4415 = KTree.node A10K2.u4413 (nat_lit 70697285) (nat_lit 6890119244) (nat_lit 0) A10K2.u4414 from rfl, allE_node, arows4413, irow4415, arows4414]
  all_goals rfl

theorem atot4415 : totK PA10K2 A10K2.u4415 = [0, 0, 0, 1920450958263, 7185094192923, 7171649963088, 1979132339439, 131938902392, 0, 0] := by
  rw [show A10K2.u4415 = KTree.node A10K2.u4413 (nat_lit 70697285) (nat_lit 6890119244) (nat_lit 0) A10K2.u4414 from rfl, totK_node, atot4413, atot4414]
  decide +kernel

theorem arows4418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4418 = true := by
  rw [show A10K2.u4418 = KTree.node A10K2.u4416 (nat_lit 70782982) (nat_lit 14882822736) (nat_lit 0) A10K2.u4417 from rfl, allE_node, arows4416, irow4418, arows4417]
  all_goals rfl

theorem atot4418 : totK PA10K2 A10K2.u4418 = [0, 1193773950094, 5040241474885, 7263006827608, 3879251427780, 1099280162303, 564424055172, 129424075521, 5976421810, 0] := by
  rw [show A10K2.u4418 = KTree.node A10K2.u4416 (nat_lit 70782982) (nat_lit 14882822736) (nat_lit 0) A10K2.u4417 from rfl, totK_node, atot4416, atot4417]
  decide +kernel

theorem arows4422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4422 = true := by
  rw [show A10K2.u4422 = KTree.node A10K2.u4420 (nat_lit 70804934) (nat_lit 15767512791) (nat_lit 0) A10K2.u4421 from rfl, allE_node, arows4420, irow4422, arows4421]
  all_goals rfl

theorem atot4422 : totK PA10K2 A10K2.u4422 = [0, 1007843049981, 5109483232363, 8250467756442, 4684714376679, 750540609528, 19519631524, 0, 0, 0] := by
  rw [show A10K2.u4422 = KTree.node A10K2.u4420 (nat_lit 70804934) (nat_lit 15767512791) (nat_lit 0) A10K2.u4421 from rfl, totK_node, atot4420, atot4421]
  decide +kernel

theorem arows4425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4425 = true := by
  rw [show A10K2.u4425 = KTree.node A10K2.u4423 (nat_lit 70815415) (nat_lit 14713829898) (nat_lit 0) A10K2.u4424 from rfl, allE_node, arows4423, irow4425, arows4424]
  all_goals rfl

theorem atot4425 : totK PA10K2 A10K2.u4425 = [0, 0, 1212461791177, 5517410663463, 7905059585336, 3889964433778, 648930276240, 30650496230, 0, 0] := by
  rw [show A10K2.u4425 = KTree.node A10K2.u4423 (nat_lit 70815415) (nat_lit 14713829898) (nat_lit 0) A10K2.u4424 from rfl, totK_node, atot4423, atot4424]
  decide +kernel

theorem arows4430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4430 = true := by
  rw [show A10K2.u4430 = KTree.node A10K2.u4428 (nat_lit 70840218) (nat_lit 13885727881) (nat_lit 0) A10K2.u4429 from rfl, allE_node, arows4428, irow4430, arows4429]
  all_goals rfl

theorem atot4430 : totK PA10K2 A10K2.u4430 = [0, 779672340784, 4221102849065, 7804670709591, 5620262533557, 1337184877114, 83315351442, 0, 0, 0] := by
  rw [show A10K2.u4430 = KTree.node A10K2.u4428 (nat_lit 70840218) (nat_lit 13885727881) (nat_lit 0) A10K2.u4429 from rfl, totK_node, atot4428, atot4429]
  decide +kernel

theorem arows4433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4433 = true := by
  rw [show A10K2.u4433 = KTree.node A10K2.u4431 (nat_lit 70987484) (nat_lit 7607656934) (nat_lit 0) A10K2.u4432 from rfl, allE_node, arows4431, irow4433, arows4432]
  all_goals rfl

theorem atot4433 : totK PA10K2 A10K2.u4433 = [0, 1132867342369, 5092021605128, 7984331215471, 4853981038317, 904330404612, 37987813032, 0, 0, 0] := by
  rw [show A10K2.u4433 = KTree.node A10K2.u4431 (nat_lit 70987484) (nat_lit 7607656934) (nat_lit 0) A10K2.u4432 from rfl, totK_node, atot4431, atot4432]
  decide +kernel

theorem arows4437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4437 = true := by
  rw [show A10K2.u4437 = KTree.node A10K2.u4435 (nat_lit 71007445) (nat_lit 5021260213) (nat_lit 0) A10K2.u4436 from rfl, allE_node, arows4435, irow4437, arows4436]
  all_goals rfl

theorem atot4437 : totK PA10K2 A10K2.u4437 = [0, 329574811601, 3003239756045, 7761235849041, 6954483587577, 1835029943866, 101344055322, 0, 0, 0] := by
  rw [show A10K2.u4437 = KTree.node A10K2.u4435 (nat_lit 71007445) (nat_lit 5021260213) (nat_lit 0) A10K2.u4436 from rfl, totK_node, atot4435, atot4436]
  decide +kernel

theorem arows4440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4440 = true := by
  rw [show A10K2.u4440 = KTree.node A10K2.u4438 (nat_lit 71019994) (nat_lit 14491231619) (nat_lit 0) A10K2.u4439 from rfl, allE_node, arows4438, irow4440, arows4439]
  all_goals rfl

theorem atot4440 : totK PA10K2 A10K2.u4440 = [0, 0, 1130469184713, 5292365121930, 8303924801838, 4577754334501, 628097472684, 13671283666, 0, 0] := by
  rw [show A10K2.u4440 = KTree.node A10K2.u4438 (nat_lit 71019994) (nat_lit 14491231619) (nat_lit 0) A10K2.u4439 from rfl, totK_node, atot4438, atot4439]
  decide +kernel

theorem arows4446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4446 = true := by
  rw [show A10K2.u4446 = KTree.node A10K2.u4444 (nat_lit 71040108) (nat_lit 4435953997) (nat_lit 0) A10K2.u4445 from rfl, allE_node, arows4444, irow4446, arows4445]
  all_goals rfl

theorem atot4446 : totK PA10K2 A10K2.u4446 = [872304469579, 2779957985724, 2851072406575, 2946474279563, 5117248527391, 4048639309685, 979338169383, 61110126106, 0, 0] := by
  rw [show A10K2.u4446 = KTree.node A10K2.u4444 (nat_lit 71040108) (nat_lit 4435953997) (nat_lit 0) A10K2.u4445 from rfl, totK_node, atot4444, atot4445]
  decide +kernel

theorem arows4449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4449 = true := by
  rw [show A10K2.u4449 = KTree.node A10K2.u4447 (nat_lit 71909740) (nat_lit 12699658009) (nat_lit 0) A10K2.u4448 from rfl, allE_node, arows4447, irow4449, arows4448]
  all_goals rfl

theorem atot4449 : totK PA10K2 A10K2.u4449 = [728110620904, 4551393804039, 8216994409429, 4798146988108, 778360355305, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4449 = KTree.node A10K2.u4447 (nat_lit 71909740) (nat_lit 12699658009) (nat_lit 0) A10K2.u4448 from rfl, totK_node, atot4447, atot4448]
  decide +kernel

theorem arows4453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4453 = true := by
  rw [show A10K2.u4453 = KTree.node A10K2.u4451 (nat_lit 71922112) (nat_lit 12025817579) (nat_lit 0) A10K2.u4452 from rfl, allE_node, arows4451, irow4453, arows4452]
  all_goals rfl

theorem atot4453 : totK PA10K2 A10K2.u4453 = [743410903023, 3906430516083, 7574782662045, 5862220515162, 1480008603593, 88159064250, 0, 0, 0, 0] := by
  rw [show A10K2.u4453 = KTree.node A10K2.u4451 (nat_lit 71922112) (nat_lit 12025817579) (nat_lit 0) A10K2.u4452 from rfl, totK_node, atot4451, atot4452]
  decide +kernel

theorem arows4456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4456 = true := by
  rw [show A10K2.u4456 = KTree.node A10K2.u4454 (nat_lit 71940436) (nat_lit 12785436927) (nat_lit 0) A10K2.u4455 from rfl, allE_node, arows4454, irow4456, arows4455]
  all_goals rfl

theorem atot4456 : totK PA10K2 A10K2.u4456 = [0, 1276062777483, 5562645103978, 7762502952025, 3749162708218, 616205234576, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4456 = KTree.node A10K2.u4454 (nat_lit 71940436) (nat_lit 12785436927) (nat_lit 0) A10K2.u4455 from rfl, totK_node, atot4454, atot4455]
  decide +kernel

theorem arows4461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4461 = true := by
  rw [show A10K2.u4461 = KTree.node A10K2.u4459 (nat_lit 71953637) (nat_lit 5232272174) (nat_lit 0) A10K2.u4460 from rfl, allE_node, arows4459, irow4461, arows4460]
  all_goals rfl

theorem atot4461 : totK PA10K2 A10K2.u4461 = [468537272203, 2798178865316, 6182497485600, 6517880324722, 2770673933101, 313939842908, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4461 = KTree.node A10K2.u4459 (nat_lit 71953637) (nat_lit 5232272174) (nat_lit 0) A10K2.u4460 from rfl, totK_node, atot4459, atot4460]
  decide +kernel

theorem arows4464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4464 = true := by
  rw [show A10K2.u4464 = KTree.node A10K2.u4462 (nat_lit 71972008) (nat_lit 6100920433) (nat_lit 0) A10K2.u4463 from rfl, allE_node, arows4462, irow4464, arows4463]
  all_goals rfl

theorem atot4464 : totK PA10K2 A10K2.u4464 = [1223287730111, 5102272834217, 7607976810371, 4491059993040, 820969541284, 37229241746, 0, 0, 0, 0] := by
  rw [show A10K2.u4464 = KTree.node A10K2.u4462 (nat_lit 71972008) (nat_lit 6100920433) (nat_lit 0) A10K2.u4463 from rfl, totK_node, atot4462, atot4463]
  decide +kernel

theorem arows4468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4468 = true := by
  rw [show A10K2.u4468 = KTree.node A10K2.u4466 (nat_lit 71981869) (nat_lit 6621766139) (nat_lit 0) A10K2.u4467 from rfl, allE_node, arows4466, irow4468, arows4467]
  all_goals rfl

theorem atot4468 : totK PA10K2 A10K2.u4468 = [366559876416, 3420826962745, 7959727618725, 5898649015640, 1270411502039, 64458694438, 0, 0, 0, 0] := by
  rw [show A10K2.u4468 = KTree.node A10K2.u4466 (nat_lit 71981869) (nat_lit 6621766139) (nat_lit 0) A10K2.u4467 from rfl, totK_node, atot4466, atot4467]
  decide +kernel

theorem arows4471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4471 = true := by
  rw [show A10K2.u4471 = KTree.node A10K2.u4469 (nat_lit 72010405) (nat_lit 7295779857) (nat_lit 0) A10K2.u4470 from rfl, allE_node, arows4469, irow4471, arows4470]
  all_goals rfl

theorem atot4471 : totK PA10K2 A10K2.u4471 = [280546762594, 2287504417371, 6368744099947, 7179270811989, 2695052718802, 329268602014, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4471 = KTree.node A10K2.u4469 (nat_lit 72010405) (nat_lit 7295779857) (nat_lit 0) A10K2.u4470 from rfl, totK_node, atot4469, atot4470]
  decide +kernel

theorem arows4479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4479 = true := by
  rw [show A10K2.u4479 = KTree.node A10K2.u4477 (nat_lit 72037790) (nat_lit 15367282906) (nat_lit 0) A10K2.u4478 from rfl, allE_node, arows4477, irow4479, arows4478]
  all_goals rfl

theorem atot4479 : totK PA10K2 A10K2.u4479 = [1330265044618, 5630525555667, 8070768625544, 4290963941872, 732519533067, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u4479 = KTree.node A10K2.u4477 (nat_lit 72037790) (nat_lit 15367282906) (nat_lit 0) A10K2.u4478 from rfl, totK_node, atot4477, atot4478]
  decide +kernel

theorem arows4482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4482 = true := by
  rw [show A10K2.u4482 = KTree.node A10K2.u4480 (nat_lit 72056417) (nat_lit 2700348911) (nat_lit 0) A10K2.u4481 from rfl, allE_node, arows4480, irow4482, arows4481]
  all_goals rfl

theorem atot4482 : totK PA10K2 A10K2.u4482 = [281487785300, 2698673149371, 7302768316410, 7214143138876, 2453409151517, 195624386581, 0, 0, 0, 0] := by
  rw [show A10K2.u4482 = KTree.node A10K2.u4480 (nat_lit 72056417) (nat_lit 2700348911) (nat_lit 0) A10K2.u4481 from rfl, totK_node, atot4480, atot4481]
  decide +kernel

theorem arows4486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4486 = true := by
  rw [show A10K2.u4486 = KTree.node A10K2.u4484 (nat_lit 72081848) (nat_lit 14495066910) (nat_lit 0) A10K2.u4485 from rfl, allE_node, arows4484, irow4486, arows4485]
  all_goals rfl

theorem atot4486 : totK PA10K2 A10K2.u4486 = [0, 1095931295581, 5398785991604, 8436792399121, 4427714814914, 612028511435, 13113983930, 0, 0, 0] := by
  rw [show A10K2.u4486 = KTree.node A10K2.u4484 (nat_lit 72081848) (nat_lit 14495066910) (nat_lit 0) A10K2.u4485 from rfl, totK_node, atot4484, atot4485]
  decide +kernel

theorem arows4489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4489 = true := by
  rw [show A10K2.u4489 = KTree.node A10K2.u4487 (nat_lit 72166037) (nat_lit 6800946018) (nat_lit 0) A10K2.u4488 from rfl, allE_node, arows4487, irow4489, arows4488]
  all_goals rfl

theorem atot4489 : totK PA10K2 A10K2.u4489 = [0, 869810279189, 4305770604992, 7540213948338, 5295767277736, 1306139634349, 86811916481, 0, 0, 0] := by
  rw [show A10K2.u4489 = KTree.node A10K2.u4487 (nat_lit 72166037) (nat_lit 6800946018) (nat_lit 0) A10K2.u4488 from rfl, totK_node, atot4487, atot4488]
  decide +kernel

theorem arows4494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4494 = true := by
  rw [show A10K2.u4494 = KTree.node A10K2.u4492 (nat_lit 72176917) (nat_lit 6954779694) (nat_lit 0) A10K2.u4493 from rfl, allE_node, arows4492, irow4494, arows4493]
  all_goals rfl

theorem atot4494 : totK PA10K2 A10K2.u4494 = [0, 1469934413965, 6071694874059, 7913135584055, 3295129565632, 339934155739, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u4494 = KTree.node A10K2.u4492 (nat_lit 72176917) (nat_lit 6954779694) (nat_lit 0) A10K2.u4493 from rfl, totK_node, atot4492, atot4493]
  decide +kernel

theorem arows4497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4497 = true := by
  rw [show A10K2.u4497 = KTree.node A10K2.u4495 (nat_lit 72197781) (nat_lit 6401147214) (nat_lit 0) A10K2.u4496 from rfl, allE_node, arows4495, irow4497, arows4496]
  all_goals rfl

theorem atot4497 : totK PA10K2 A10K2.u4497 = [0, 0, 1782943651270, 6704820741090, 7595954068786, 2886634788074, 438895052468, 25565504801, 0, 0] := by
  rw [show A10K2.u4497 = KTree.node A10K2.u4495 (nat_lit 72197781) (nat_lit 6401147214) (nat_lit 0) A10K2.u4496 from rfl, totK_node, atot4495, atot4496]
  decide +kernel

theorem arows4501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4501 = true := by
  rw [show A10K2.u4501 = KTree.node A10K2.u4499 (nat_lit 72207034) (nat_lit 13783440098) (nat_lit 0) A10K2.u4500 from rfl, allE_node, arows4499, irow4501, arows4500]
  all_goals rfl

theorem atot4501 : totK PA10K2 A10K2.u4501 = [0, 0, 1414364157029, 5791669006038, 7708339898234, 3371302250568, 441915159207, 11138589073, 0, 0] := by
  rw [show A10K2.u4501 = KTree.node A10K2.u4499 (nat_lit 72207034) (nat_lit 13783440098) (nat_lit 0) A10K2.u4500 from rfl, totK_node, atot4499, atot4500]
  decide +kernel

theorem arows4504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4504 = true := by
  rw [show A10K2.u4504 = KTree.node A10K2.u4502 (nat_lit 72227692) (nat_lit 11327994125) (nat_lit 0) A10K2.u4503 from rfl, allE_node, arows4502, irow4504, arows4503]
  all_goals rfl

theorem atot4504 : totK PA10K2 A10K2.u4504 = [0, 1268414326845, 5438261585483, 7818092854435, 4111228013316, 732074692128, 36736648791, 0, 0, 0] := by
  rw [show A10K2.u4504 = KTree.node A10K2.u4502 (nat_lit 72227692) (nat_lit 11327994125) (nat_lit 0) A10K2.u4503 from rfl, totK_node, atot4502, atot4503]
  decide +kernel

theorem arows4510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4510 = true := by
  rw [show A10K2.u4510 = KTree.node A10K2.u4508 (nat_lit 72239027) (nat_lit 9835917421) (nat_lit 0) A10K2.u4509 from rfl, allE_node, arows4508, irow4510, arows4509]
  all_goals rfl

theorem atot4510 : totK PA10K2 A10K2.u4510 = [0, 789970551885, 4340723384022, 7809397425658, 4911651630604, 898295848251, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u4510 = KTree.node A10K2.u4508 (nat_lit 72239027) (nat_lit 9835917421) (nat_lit 0) A10K2.u4509 from rfl, totK_node, atot4508, atot4509]
  decide +kernel

theorem arows4513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4513 = true := by
  rw [show A10K2.u4513 = KTree.node A10K2.u4511 (nat_lit 72265430) (nat_lit 13857455717) (nat_lit 0) A10K2.u4512 from rfl, allE_node, arows4511, irow4513, arows4512]
  all_goals rfl

theorem atot4513 : totK PA10K2 A10K2.u4513 = [0, 0, 1846878518309, 7101114289448, 7744164742615, 2043770728422, 119591524282, 0, 0, 0] := by
  rw [show A10K2.u4513 = KTree.node A10K2.u4511 (nat_lit 72265430) (nat_lit 13857455717) (nat_lit 0) A10K2.u4512 from rfl, totK_node, atot4511, atot4512]
  decide +kernel

theorem arows4517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4517 = true := by
  rw [show A10K2.u4517 = KTree.node A10K2.u4515 (nat_lit 72296183) (nat_lit 10803467008) (nat_lit 0) A10K2.u4516 from rfl, allE_node, arows4515, irow4517, arows4516]
  all_goals rfl

theorem atot4517 : totK PA10K2 A10K2.u4517 = [0, 1089773727774, 4791151453094, 7267827644147, 4792824003821, 1495196208639, 202410208075, 6239673734, 0, 0] := by
  rw [show A10K2.u4517 = KTree.node A10K2.u4515 (nat_lit 72296183) (nat_lit 10803467008) (nat_lit 0) A10K2.u4516 from rfl, totK_node, atot4515, atot4516]
  decide +kernel

theorem arows4520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4520 = true := by
  rw [show A10K2.u4520 = KTree.node A10K2.u4518 (nat_lit 72314757) (nat_lit 2559820636) (nat_lit 0) A10K2.u4519 from rfl, allE_node, arows4518, irow4520, arows4519]
  all_goals rfl

theorem atot4520 : totK PA10K2 A10K2.u4520 = [301604122727, 1562578312375, 4449710036501, 7259317190304, 5225425815193, 1244486620886, 68006876977, 0, 0, 0] := by
  rw [show A10K2.u4520 = KTree.node A10K2.u4518 (nat_lit 72314757) (nat_lit 2559820636) (nat_lit 0) A10K2.u4519 from rfl, totK_node, atot4518, atot4519]
  decide +kernel

theorem arows4525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4525 = true := by
  rw [show A10K2.u4525 = KTree.node A10K2.u4523 (nat_lit 72358122) (nat_lit 9296503236) (nat_lit 0) A10K2.u4524 from rfl, allE_node, arows4523, irow4525, arows4524]
  all_goals rfl

theorem atot4525 : totK PA10K2 A10K2.u4525 = [1237056671062, 5550813176535, 7923057430016, 3980757005506, 666427091076, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4525 = KTree.node A10K2.u4523 (nat_lit 72358122) (nat_lit 9296503236) (nat_lit 0) A10K2.u4524 from rfl, totK_node, atot4523, atot4524]
  decide +kernel

theorem arows4528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4528 = true := by
  rw [show A10K2.u4528 = KTree.node A10K2.u4526 (nat_lit 72386900) (nat_lit 12801064028) (nat_lit 0) A10K2.u4527 from rfl, allE_node, arows4526, irow4528, arows4527]
  all_goals rfl

theorem atot4528 : totK PA10K2 A10K2.u4528 = [0, 1681771593795, 6207310628343, 7226950829871, 3325460030349, 587379814945, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4528 = KTree.node A10K2.u4526 (nat_lit 72386900) (nat_lit 12801064028) (nat_lit 0) A10K2.u4527 from rfl, totK_node, atot4526, atot4527]
  decide +kernel

theorem arows4532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4532 = true := by
  rw [show A10K2.u4532 = KTree.node A10K2.u4530 (nat_lit 72407191) (nat_lit 7958571711) (nat_lit 0) A10K2.u4531 from rfl, allE_node, arows4530, irow4532, arows4531]
  all_goals rfl

theorem atot4532 : totK PA10K2 A10K2.u4532 = [836243354860, 3683579712853, 6462368563356, 5807795254502, 2116483028238, 230692190195, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4532 = KTree.node A10K2.u4530 (nat_lit 72407191) (nat_lit 7958571711) (nat_lit 0) A10K2.u4531 from rfl, totK_node, atot4530, atot4531]
  decide +kernel

theorem arows4535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4535 = true := by
  rw [show A10K2.u4535 = KTree.node A10K2.u4533 (nat_lit 72434902) (nat_lit 14055641635) (nat_lit 0) A10K2.u4534 from rfl, allE_node, arows4533, irow4535, arows4534]
  all_goals rfl

theorem atot4535 : totK PA10K2 A10K2.u4535 = [770689108024, 4442932025946, 8117903786555, 4943699975057, 814545616835, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4535 = KTree.node A10K2.u4533 (nat_lit 72434902) (nat_lit 14055641635) (nat_lit 0) A10K2.u4534 from rfl, totK_node, atot4533, atot4534]
  decide +kernel

theorem arows4542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4542 = true := by
  rw [show A10K2.u4542 = KTree.node A10K2.u4540 (nat_lit 72449422) (nat_lit 15177716178) (nat_lit 0) A10K2.u4541 from rfl, allE_node, arows4540, irow4542, arows4541]
  all_goals rfl

theorem atot4542 : totK PA10K2 A10K2.u4542 = [554803763168, 3428108935601, 7481722921827, 6357755641766, 1681095084007, 95403658426, 0, 0, 0, 0] := by
  rw [show A10K2.u4542 = KTree.node A10K2.u4540 (nat_lit 72449422) (nat_lit 15177716178) (nat_lit 0) A10K2.u4541 from rfl, totK_node, atot4540, atot4541]
  decide +kernel

theorem arows4545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4545 = true := by
  rw [show A10K2.u4545 = KTree.node A10K2.u4543 (nat_lit 72467777) (nat_lit 8598464661) (nat_lit 0) A10K2.u4544 from rfl, allE_node, arows4543, irow4545, arows4544]
  all_goals rfl

theorem atot4545 : totK PA10K2 A10K2.u4545 = [0, 812972056043, 4457799807320, 7998250348771, 4736207625477, 816273369049, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4545 = KTree.node A10K2.u4543 (nat_lit 72467777) (nat_lit 8598464661) (nat_lit 0) A10K2.u4544 from rfl, totK_node, atot4543, atot4544]
  decide +kernel

theorem arows4549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4549 = true := by
  rw [show A10K2.u4549 = KTree.node A10K2.u4547 (nat_lit 72485190) (nat_lit 9672223195) (nat_lit 0) A10K2.u4548 from rfl, allE_node, arows4547, irow4549, arows4548]
  all_goals rfl

theorem atot4549 : totK PA10K2 A10K2.u4549 = [951328283053, 4425302063768, 7363850298143, 5168602946954, 1385791917080, 100600184663, 0, 0, 0, 0] := by
  rw [show A10K2.u4549 = KTree.node A10K2.u4547 (nat_lit 72485190) (nat_lit 9672223195) (nat_lit 0) A10K2.u4548 from rfl, totK_node, atot4547, atot4548]
  decide +kernel

theorem arows4552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4552 = true := by
  rw [show A10K2.u4552 = KTree.node A10K2.u4550 (nat_lit 72497435) (nat_lit 9956983286) (nat_lit 0) A10K2.u4551 from rfl, allE_node, arows4550, irow4552, arows4551]
  all_goals rfl

theorem atot4552 : totK PA10K2 A10K2.u4552 = [1303244906413, 5471057833069, 7682492476198, 4034797943688, 694383591327, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4552 = KTree.node A10K2.u4550 (nat_lit 72497435) (nat_lit 9956983286) (nat_lit 0) A10K2.u4551 from rfl, totK_node, atot4550, atot4551]
  decide +kernel

theorem arows4557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4557 = true := by
  rw [show A10K2.u4557 = KTree.node A10K2.u4555 (nat_lit 72517750) (nat_lit 10073280064) (nat_lit 0) A10K2.u4556 from rfl, allE_node, arows4555, irow4557, arows4556]
  all_goals rfl

theorem atot4557 : totK PA10K2 A10K2.u4557 = [0, 2456021161393, 7984586567266, 7000360833417, 1636985233234, 77608611860, 0, 0, 0, 0] := by
  rw [show A10K2.u4557 = KTree.node A10K2.u4555 (nat_lit 72517750) (nat_lit 10073280064) (nat_lit 0) A10K2.u4556 from rfl, totK_node, atot4555, atot4556]
  decide +kernel

theorem arows4560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4560 = true := by
  rw [show A10K2.u4560 = KTree.node A10K2.u4558 (nat_lit 72536421) (nat_lit 7275093894) (nat_lit 0) A10K2.u4559 from rfl, allE_node, arows4558, irow4560, arows4559]
  all_goals rfl

theorem atot4560 : totK PA10K2 A10K2.u4560 = [0, 1472521929501, 6118660072501, 7888581136321, 3016929212412, 354954654880, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4560 = KTree.node A10K2.u4558 (nat_lit 72536421) (nat_lit 7275093894) (nat_lit 0) A10K2.u4559 from rfl, totK_node, atot4558, atot4559]
  decide +kernel

theorem arows4564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4564 = true := by
  rw [show A10K2.u4564 = KTree.node A10K2.u4562 (nat_lit 72630816) (nat_lit 14183516647) (nat_lit 0) A10K2.u4563 from rfl, allE_node, arows4562, irow4564, arows4563]
  all_goals rfl

theorem atot4564 : totK PA10K2 A10K2.u4564 = [0, 896880587696, 4905268488456, 8179416759519, 4505807191890, 725642396679, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u4564 = KTree.node A10K2.u4562 (nat_lit 72630816) (nat_lit 14183516647) (nat_lit 0) A10K2.u4563 from rfl, totK_node, atot4562, atot4563]
  decide +kernel

theorem arows4567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4567 = true := by
  rw [show A10K2.u4567 = KTree.node A10K2.u4565 (nat_lit 72692883) (nat_lit 11041069466) (nat_lit 0) A10K2.u4566 from rfl, allE_node, arows4565, irow4567, arows4566]
  all_goals rfl

theorem atot4567 : totK PA10K2 A10K2.u4567 = [0, 1237209167903, 5082161563246, 7523471165093, 4408685985673, 817941468700, 37807056478, 0, 0, 0] := by
  rw [show A10K2.u4567 = KTree.node A10K2.u4565 (nat_lit 72692883) (nat_lit 11041069466) (nat_lit 0) A10K2.u4566 from rfl, totK_node, atot4565, atot4566]
  decide +kernel

theorem arows4573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4573 = true := by
  rw [show A10K2.u4573 = KTree.node A10K2.u4571 (nat_lit 72702824) (nat_lit 8866611563) (nat_lit 0) A10K2.u4572 from rfl, allE_node, arows4571, irow4573, arows4572]
  all_goals rfl

theorem atot4573 : totK PA10K2 A10K2.u4573 = [0, 967176092697, 5035885397163, 8327961809613, 4496895705760, 636475150875, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u4573 = KTree.node A10K2.u4571 (nat_lit 72702824) (nat_lit 8866611563) (nat_lit 0) A10K2.u4572 from rfl, totK_node, atot4571, atot4572]
  decide +kernel

theorem arows4576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4576 = true := by
  rw [show A10K2.u4576 = KTree.node A10K2.u4574 (nat_lit 72751336) (nat_lit 7370953194) (nat_lit 0) A10K2.u4575 from rfl, allE_node, arows4574, irow4576, arows4575]
  all_goals rfl

theorem atot4576 : totK PA10K2 A10K2.u4576 = [0, 1373312387627, 5857426840414, 7824725211627, 3555967329941, 525976829638, 30074883546, 0, 0, 0] := by
  rw [show A10K2.u4576 = KTree.node A10K2.u4574 (nat_lit 72751336) (nat_lit 7370953194) (nat_lit 0) A10K2.u4575 from rfl, totK_node, atot4574, atot4575]
  decide +kernel

theorem arows4580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4580 = true := by
  rw [show A10K2.u4580 = KTree.node A10K2.u4578 (nat_lit 72762774) (nat_lit 12225003464) (nat_lit 0) A10K2.u4579 from rfl, allE_node, arows4578, irow4580, arows4579]
  all_goals rfl

theorem atot4580 : totK PA10K2 A10K2.u4580 = [0, 836002267270, 4509891758925, 8027842529258, 4624033306786, 716030339460, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u4580 = KTree.node A10K2.u4578 (nat_lit 72762774) (nat_lit 12225003464) (nat_lit 0) A10K2.u4579 from rfl, totK_node, atot4578, atot4579]
  decide +kernel

theorem arows4583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4583 = true := by
  rw [show A10K2.u4583 = KTree.node A10K2.u4581 (nat_lit 72788197) (nat_lit 7119318088) (nat_lit 0) A10K2.u4582 from rfl, allE_node, arows4581, irow4583, arows4582]
  all_goals rfl

theorem atot4583 : totK PA10K2 A10K2.u4583 = [0, 0, 2229913420434, 7533683596282, 7044508393325, 1768435762868, 119348013684, 0, 0, 0] := by
  rw [show A10K2.u4583 = KTree.node A10K2.u4581 (nat_lit 72788197) (nat_lit 7119318088) (nat_lit 0) A10K2.u4582 from rfl, totK_node, atot4581, atot4582]
  decide +kernel

theorem arows4588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4588 = true := by
  rw [show A10K2.u4588 = KTree.node A10K2.u4586 (nat_lit 72952042) (nat_lit 12436460845) (nat_lit 0) A10K2.u4587 from rfl, allE_node, arows4586, irow4588, arows4587]
  all_goals rfl

theorem atot4588 : totK PA10K2 A10K2.u4588 = [845571698839, 3651532009770, 5397880413083, 4069083320561, 3156382003278, 1608915304094, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u4588 = KTree.node A10K2.u4586 (nat_lit 72952042) (nat_lit 12436460845) (nat_lit 0) A10K2.u4587 from rfl, totK_node, atot4586, atot4587]
  decide +kernel

theorem arows4591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4591 = true := by
  rw [show A10K2.u4591 = KTree.node A10K2.u4589 (nat_lit 72964379) (nat_lit 9557261042) (nat_lit 0) A10K2.u4590 from rfl, allE_node, arows4589, irow4591, arows4590]
  all_goals rfl

theorem atot4591 : totK PA10K2 A10K2.u4591 = [1365456076752, 5961911694502, 8239806675711, 3772783746592, 500185405361, 12388698189, 0, 0, 0, 0] := by
  rw [show A10K2.u4591 = KTree.node A10K2.u4589 (nat_lit 72964379) (nat_lit 9557261042) (nat_lit 0) A10K2.u4590 from rfl, totK_node, atot4589, atot4590]
  decide +kernel

theorem arows4595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4595 = true := by
  rw [show A10K2.u4595 = KTree.node A10K2.u4593 (nat_lit 72984364) (nat_lit 12696003021) (nat_lit 0) A10K2.u4594 from rfl, allE_node, arows4593, irow4595, arows4594]
  all_goals rfl

theorem atot4595 : totK PA10K2 A10K2.u4595 = [0, 1529881063544, 6308417232482, 7974836064920, 3354220728458, 493533271041, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u4595 = KTree.node A10K2.u4593 (nat_lit 72984364) (nat_lit 12696003021) (nat_lit 0) A10K2.u4594 from rfl, totK_node, atot4593, atot4594]
  decide +kernel

theorem arows4598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4598 = true := by
  rw [show A10K2.u4598 = KTree.node A10K2.u4596 (nat_lit 72996970) (nat_lit 5493577187) (nat_lit 0) A10K2.u4597 from rfl, allE_node, arows4596, irow4598, arows4597]
  all_goals rfl

theorem atot4598 : totK PA10K2 A10K2.u4598 = [0, 1364129328507, 5870347142759, 8124077630817, 3700671549171, 453401638512, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u4598 = KTree.node A10K2.u4596 (nat_lit 72996970) (nat_lit 5493577187) (nat_lit 0) A10K2.u4597 from rfl, totK_node, atot4596, atot4597]
  decide +kernel

theorem arows4608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4608 = true := by
  rw [show A10K2.u4608 = KTree.node A10K2.u4606 (nat_lit 73080023) (nat_lit 12666872112) (nat_lit 0) A10K2.u4607 from rfl, allE_node, arows4606, irow4608, arows4607]
  all_goals rfl

theorem atot4608 : totK PA10K2 A10K2.u4608 = [1377134623178, 5867901083835, 8095926360581, 3931246517398, 730649056153, 62896129269, 0, 0, 0, 0] := by
  rw [show A10K2.u4608 = KTree.node A10K2.u4606 (nat_lit 73080023) (nat_lit 12666872112) (nat_lit 0) A10K2.u4607 from rfl, totK_node, atot4606, atot4607]
  decide +kernel

theorem arows4611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4611 = true := by
  rw [show A10K2.u4611 = KTree.node A10K2.u4609 (nat_lit 73099036) (nat_lit 9907558672) (nat_lit 0) A10K2.u4610 from rfl, allE_node, arows4609, irow4611, arows4610]
  all_goals rfl

theorem atot4611 : totK PA10K2 A10K2.u4611 = [868342544860, 4501650357716, 8047814823560, 5416510708409, 1100062235114, 45493318729, 0, 0, 0, 0] := by
  rw [show A10K2.u4611 = KTree.node A10K2.u4609 (nat_lit 73099036) (nat_lit 9907558672) (nat_lit 0) A10K2.u4610 from rfl, totK_node, atot4609, atot4610]
  decide +kernel

theorem arows4615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4615 = true := by
  rw [show A10K2.u4615 = KTree.node A10K2.u4613 (nat_lit 73109951) (nat_lit 14166159072) (nat_lit 0) A10K2.u4614 from rfl, allE_node, arows4613, irow4615, arows4614]
  all_goals rfl

theorem atot4615 : totK PA10K2 A10K2.u4615 = [0, 1496916497866, 6245259585603, 8241527437105, 3624832751831, 436897739813, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4615 = KTree.node A10K2.u4613 (nat_lit 73109951) (nat_lit 14166159072) (nat_lit 0) A10K2.u4614 from rfl, totK_node, atot4613, atot4614]
  decide +kernel

theorem arows4618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4618 = true := by
  rw [show A10K2.u4618 = KTree.node A10K2.u4616 (nat_lit 73131510) (nat_lit 16668028827) (nat_lit 0) A10K2.u4617 from rfl, allE_node, arows4616, irow4618, arows4617]
  all_goals rfl

theorem atot4618 : totK PA10K2 A10K2.u4618 = [0, 867053287319, 4715995834277, 8340018760156, 5148816839249, 798329678249, 19271132487, 0, 0, 0] := by
  rw [show A10K2.u4618 = KTree.node A10K2.u4616 (nat_lit 73131510) (nat_lit 16668028827) (nat_lit 0) A10K2.u4617 from rfl, totK_node, atot4616, atot4617]
  decide +kernel

theorem arows4623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4623 = true := by
  rw [show A10K2.u4623 = KTree.node A10K2.u4621 (nat_lit 73215438) (nat_lit 14630697666) (nat_lit 0) A10K2.u4622 from rfl, allE_node, arows4621, irow4623, arows4622]
  all_goals rfl

theorem atot4623 : totK PA10K2 A10K2.u4623 = [0, 1096852591233, 4770435815852, 7465799230523, 4927773772536, 1177881551221, 80192943509, 0, 0, 0] := by
  rw [show A10K2.u4623 = KTree.node A10K2.u4621 (nat_lit 73215438) (nat_lit 14630697666) (nat_lit 0) A10K2.u4622 from rfl, totK_node, atot4621, atot4622]
  decide +kernel

theorem arows4626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4626 = true := by
  rw [show A10K2.u4626 = KTree.node A10K2.u4624 (nat_lit 73229239) (nat_lit 15026248115) (nat_lit 0) A10K2.u4625 from rfl, allE_node, arows4624, irow4626, arows4625]
  all_goals rfl

theorem atot4626 : totK PA10K2 A10K2.u4626 = [0, 1114175184358, 5443854604121, 8412658192714, 4295085181316, 593226317418, 12519525618, 0, 0, 0] := by
  rw [show A10K2.u4626 = KTree.node A10K2.u4624 (nat_lit 73229239) (nat_lit 15026248115) (nat_lit 0) A10K2.u4625 from rfl, totK_node, atot4624, atot4625]
  decide +kernel

theorem arows4630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4630 = true := by
  rw [show A10K2.u4630 = KTree.node A10K2.u4628 (nat_lit 73247900) (nat_lit 10655187567) (nat_lit 0) A10K2.u4629 from rfl, allE_node, arows4628, irow4630, arows4629]
  all_goals rfl

theorem atot4630 : totK PA10K2 A10K2.u4630 = [0, 0, 1585719593518, 6266928833404, 8002973206080, 3335628269959, 391753770172, 7151180950, 0, 0] := by
  rw [show A10K2.u4630 = KTree.node A10K2.u4628 (nat_lit 73247900) (nat_lit 10655187567) (nat_lit 0) A10K2.u4629 from rfl, totK_node, atot4628, atot4629]
  decide +kernel

theorem arows4633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4633 = true := by
  rw [show A10K2.u4633 = KTree.node A10K2.u4631 (nat_lit 73265150) (nat_lit 15844512021) (nat_lit 0) A10K2.u4632 from rfl, allE_node, arows4631, irow4633, arows4632]
  all_goals rfl

theorem atot4633 : totK PA10K2 A10K2.u4633 = [0, 592737332747, 3653029348951, 7784848408263, 6299217785119, 1630602130312, 87180972706, 0, 0, 0] := by
  rw [show A10K2.u4633 = KTree.node A10K2.u4631 (nat_lit 73265150) (nat_lit 15844512021) (nat_lit 0) A10K2.u4632 from rfl, totK_node, atot4631, atot4632]
  decide +kernel

theorem arows4639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4639 = true := by
  rw [show A10K2.u4639 = KTree.node A10K2.u4637 (nat_lit 73348599) (nat_lit 14690530377) (nat_lit 0) A10K2.u4638 from rfl, allE_node, arows4637, irow4639, arows4638]
  all_goals rfl

theorem atot4639 : totK PA10K2 A10K2.u4639 = [0, 1407171832497, 5788461404016, 8016153486708, 4063446124094, 576392934918, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u4639 = KTree.node A10K2.u4637 (nat_lit 73348599) (nat_lit 14690530377) (nat_lit 0) A10K2.u4638 from rfl, totK_node, atot4637, atot4638]
  decide +kernel

theorem arows4642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4642 = true := by
  rw [show A10K2.u4642 = KTree.node A10K2.u4640 (nat_lit 73367027) (nat_lit 8717450873) (nat_lit 0) A10K2.u4641 from rfl, allE_node, arows4640, irow4642, arows4641]
  all_goals rfl

theorem atot4642 : totK PA10K2 A10K2.u4642 = [0, 244073525254, 2550934892212, 7037580341156, 7308855443969, 2626984445270, 267896749353, 6318667960, 0, 0] := by
  rw [show A10K2.u4642 = KTree.node A10K2.u4640 (nat_lit 73367027) (nat_lit 8717450873) (nat_lit 0) A10K2.u4641 from rfl, totK_node, atot4640, atot4641]
  decide +kernel

theorem arows4646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4646 = true := by
  rw [show A10K2.u4646 = KTree.node A10K2.u4644 (nat_lit 73381100) (nat_lit 9266767738) (nat_lit 0) A10K2.u4645 from rfl, allE_node, arows4644, irow4646, arows4645]
  all_goals rfl

theorem atot4646 : totK PA10K2 A10K2.u4646 = [0, 0, 1457302317524, 6118661155558, 8186334083067, 3638736002315, 391066797628, 6439430839, 0, 0] := by
  rw [show A10K2.u4646 = KTree.node A10K2.u4644 (nat_lit 73381100) (nat_lit 9266767738) (nat_lit 0) A10K2.u4645 from rfl, totK_node, atot4644, atot4645]
  decide +kernel

theorem arows4649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4649 = true := by
  rw [show A10K2.u4649 = KTree.node A10K2.u4647 (nat_lit 73399959) (nat_lit 14036657062) (nat_lit 0) A10K2.u4648 from rfl, allE_node, arows4647, irow4649, arows4648]
  all_goals rfl

theorem atot4649 : totK PA10K2 A10K2.u4649 = [0, 871367436928, 3376601828664, 5193621165867, 5385840617908, 3762876085031, 961189328672, 61018386929, 0, 0] := by
  rw [show A10K2.u4649 = KTree.node A10K2.u4647 (nat_lit 73399959) (nat_lit 14036657062) (nat_lit 0) A10K2.u4648 from rfl, totK_node, atot4647, atot4648]
  decide +kernel

theorem arows4654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4654 = true := by
  rw [show A10K2.u4654 = KTree.node A10K2.u4652 (nat_lit 74007907) (nat_lit 9355842215) (nat_lit 0) A10K2.u4653 from rfl, allE_node, arows4652, irow4654, arows4653]
  all_goals rfl

theorem atot4654 : totK PA10K2 A10K2.u4654 = [0, 791870582519, 4336408865015, 7850002599878, 4922712346584, 877348009159, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u4654 = KTree.node A10K2.u4652 (nat_lit 74007907) (nat_lit 9355842215) (nat_lit 0) A10K2.u4653 from rfl, totK_node, atot4652, atot4653]
  decide +kernel

theorem arows4657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4657 = true := by
  rw [show A10K2.u4657 = KTree.node A10K2.u4655 (nat_lit 74020279) (nat_lit 15077211702) (nat_lit 0) A10K2.u4656 from rfl, allE_node, arows4655, irow4657, arows4656]
  all_goals rfl

theorem atot4657 : totK PA10K2 A10K2.u4657 = [0, 676882298558, 3934183160770, 7777489260481, 5847190400839, 1396059985844, 74019108011, 0, 0, 0] := by
  rw [show A10K2.u4657 = KTree.node A10K2.u4655 (nat_lit 74020279) (nat_lit 15077211702) (nat_lit 0) A10K2.u4656 from rfl, totK_node, atot4655, atot4656]
  decide +kernel

theorem arows4661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4661 = true := by
  rw [show A10K2.u4661 = KTree.node A10K2.u4659 (nat_lit 74038704) (nat_lit 12855199912) (nat_lit 0) A10K2.u4660 from rfl, allE_node, arows4659, irow4661, arows4660]
  all_goals rfl

theorem atot4661 : totK PA10K2 A10K2.u4661 = [0, 0, 1011676056590, 5053569397723, 7998023742632, 4127300217791, 661475797149, 31082886609, 0, 0] := by
  rw [show A10K2.u4661 = KTree.node A10K2.u4659 (nat_lit 74038704) (nat_lit 12855199912) (nat_lit 0) A10K2.u4660 from rfl, totK_node, atot4659, atot4660]
  decide +kernel

theorem arows4664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4664 = true := by
  rw [show A10K2.u4664 = KTree.node A10K2.u4662 (nat_lit 74051525) (nat_lit 1727964361) (nat_lit 0) A10K2.u4663 from rfl, allE_node, arows4662, irow4664, arows4663]
  all_goals rfl

theorem atot4664 : totK PA10K2 A10K2.u4664 = [0, 777954947991, 3772402028560, 6707058444197, 5568175357505, 2039846333377, 240806217386, 6121173289, 0, 0] := by
  rw [show A10K2.u4664 = KTree.node A10K2.u4662 (nat_lit 74051525) (nat_lit 1727964361) (nat_lit 0) A10K2.u4663 from rfl, totK_node, atot4662, atot4663]
  decide +kernel

theorem arows4671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4671 = true := by
  rw [show A10K2.u4671 = KTree.node A10K2.u4669 (nat_lit 74070228) (nat_lit 11753543645) (nat_lit 0) A10K2.u4670 from rfl, allE_node, arows4669, irow4671, arows4670]
  all_goals rfl

theorem atot4671 : totK PA10K2 A10K2.u4671 = [0, 1278612021435, 5439012498631, 7705307189956, 4109771646737, 704508044403, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4671 = KTree.node A10K2.u4669 (nat_lit 74070228) (nat_lit 11753543645) (nat_lit 0) A10K2.u4670 from rfl, totK_node, atot4669, atot4670]
  decide +kernel

theorem arows4674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4674 = true := by
  rw [show A10K2.u4674 = KTree.node A10K2.u4672 (nat_lit 74091014) (nat_lit 10373551654) (nat_lit 0) A10K2.u4673 from rfl, allE_node, arows4672, irow4674, arows4673]
  all_goals rfl

theorem atot4674 : totK PA10K2 A10K2.u4674 = [0, 0, 2517200473794, 8092337082652, 6839965849312, 1456150958545, 57439356141, 0, 0, 0] := by
  rw [show A10K2.u4674 = KTree.node A10K2.u4672 (nat_lit 74091014) (nat_lit 10373551654) (nat_lit 0) A10K2.u4673 from rfl, totK_node, atot4672, atot4673]
  decide +kernel

theorem arows4678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4678 = true := by
  rw [show A10K2.u4678 = KTree.node A10K2.u4676 (nat_lit 74111260) (nat_lit 12202579886) (nat_lit 0) A10K2.u4677 from rfl, allE_node, arows4676, irow4678, arows4677]
  all_goals rfl

theorem atot4678 : totK PA10K2 A10K2.u4678 = [0, 794672530841, 3496592041212, 6498087082828, 6105527954836, 2107179943648, 245550992532, 6354482628, 0, 0] := by
  rw [show A10K2.u4678 = KTree.node A10K2.u4676 (nat_lit 74111260) (nat_lit 12202579886) (nat_lit 0) A10K2.u4677 from rfl, totK_node, atot4676, atot4677]
  decide +kernel

theorem arows4681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4681 = true := by
  rw [show A10K2.u4681 = KTree.node A10K2.u4679 (nat_lit 74136798) (nat_lit 11418968776) (nat_lit 0) A10K2.u4680 from rfl, allE_node, arows4679, irow4681, arows4680]
  all_goals rfl

theorem atot4681 : totK PA10K2 A10K2.u4681 = [0, 1096690526325, 5315109905353, 8300399069343, 4520246213414, 734615245612, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u4681 = KTree.node A10K2.u4679 (nat_lit 74136798) (nat_lit 11418968776) (nat_lit 0) A10K2.u4680 from rfl, totK_node, atot4679, atot4680]
  decide +kernel

theorem arows4686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4686 = true := by
  rw [show A10K2.u4686 = KTree.node A10K2.u4684 (nat_lit 74161201) (nat_lit 9349012681) (nat_lit 0) A10K2.u4685 from rfl, allE_node, arows4684, irow4686, arows4685]
  all_goals rfl

theorem atot4686 : totK PA10K2 A10K2.u4686 = [0, 0, 1696581605595, 6801148159802, 8223271229990, 3056755991471, 238180037291, 0, 0, 0] := by
  rw [show A10K2.u4686 = KTree.node A10K2.u4684 (nat_lit 74161201) (nat_lit 9349012681) (nat_lit 0) A10K2.u4685 from rfl, totK_node, atot4684, atot4685]
  decide +kernel

theorem arows4689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4689 = true := by
  rw [show A10K2.u4689 = KTree.node A10K2.u4687 (nat_lit 74181787) (nat_lit 9878357186) (nat_lit 0) A10K2.u4688 from rfl, allE_node, arows4687, irow4689, arows4688]
  all_goals rfl

theorem atot4689 : totK PA10K2 A10K2.u4689 = [0, 0, 798712068457, 4415128604814, 8194403951936, 5520333283355, 972828470189, 19026474010, 0, 0] := by
  rw [show A10K2.u4689 = KTree.node A10K2.u4687 (nat_lit 74181787) (nat_lit 9878357186) (nat_lit 0) A10K2.u4688 from rfl, totK_node, atot4687, atot4688]
  decide +kernel

theorem arows4693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4693 = true := by
  rw [show A10K2.u4693 = KTree.node A10K2.u4691 (nat_lit 74265939) (nat_lit 10550511040) (nat_lit 0) A10K2.u4692 from rfl, allE_node, arows4691, irow4693, arows4692]
  all_goals rfl

theorem atot4693 : totK PA10K2 A10K2.u4693 = [0, 0, 1311382743217, 5518125607320, 7587588497169, 3967038300851, 791346965767, 60919595321, 0, 0] := by
  rw [show A10K2.u4693 = KTree.node A10K2.u4691 (nat_lit 74265939) (nat_lit 10550511040) (nat_lit 0) A10K2.u4692 from rfl, totK_node, atot4691, atot4692]
  decide +kernel

theorem arows4696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4696 = true := by
  rw [show A10K2.u4696 = KTree.node A10K2.u4694 (nat_lit 74278125) (nat_lit 5777220573) (nat_lit 0) A10K2.u4695 from rfl, allE_node, arows4694, irow4696, arows4695]
  all_goals rfl

theorem atot4696 : totK PA10K2 A10K2.u4696 = [0, 0, 1020661487703, 5151116062100, 8273410204914, 4213363859382, 563201910580, 13202416085, 0, 0] := by
  rw [show A10K2.u4696 = KTree.node A10K2.u4694 (nat_lit 74278125) (nat_lit 5777220573) (nat_lit 0) A10K2.u4695 from rfl, totK_node, atot4694, atot4695]
  decide +kernel

theorem arows4702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4702 = true := by
  rw [show A10K2.u4702 = KTree.node A10K2.u4700 (nat_lit 74297266) (nat_lit 14335716078) (nat_lit 0) A10K2.u4701 from rfl, allE_node, arows4700, irow4702, arows4701]
  all_goals rfl

theorem atot4702 : totK PA10K2 A10K2.u4702 = [0, 0, 0, 1412268874148, 5773462306479, 7486015523003, 3550318523220, 619701190211, 31018567651, 0] := by
  rw [show A10K2.u4702 = KTree.node A10K2.u4700 (nat_lit 74297266) (nat_lit 14335716078) (nat_lit 0) A10K2.u4701 from rfl, totK_node, atot4700, atot4701]
  decide +kernel

theorem arows4705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4705 = true := by
  rw [show A10K2.u4705 = KTree.node A10K2.u4703 (nat_lit 74310884) (nat_lit 12060166883) (nat_lit 0) A10K2.u4704 from rfl, allE_node, arows4703, irow4705, arows4704]
  all_goals rfl

theorem atot4705 : totK PA10K2 A10K2.u4705 = [0, 0, 468537272203, 2808555592828, 6413846716639, 6461636213405, 2391310833607, 268873873207, 5685526223, 0] := by
  rw [show A10K2.u4705 = KTree.node A10K2.u4703 (nat_lit 74310884) (nat_lit 12060166883) (nat_lit 0) A10K2.u4704 from rfl, totK_node, atot4703, atot4704]
  decide +kernel

theorem arows4709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4709 = true := by
  rw [show A10K2.u4709 = KTree.node A10K2.u4707 (nat_lit 74329811) (nat_lit 10602640485) (nat_lit 0) A10K2.u4708 from rfl, allE_node, arows4707, irow4709, arows4708]
  all_goals rfl

theorem atot4709 : totK PA10K2 A10K2.u4709 = [0, 0, 1116872625167, 4949918532701, 7771084056009, 4385059653762, 758641199314, 37229241746, 0, 0] := by
  rw [show A10K2.u4709 = KTree.node A10K2.u4707 (nat_lit 74329811) (nat_lit 10602640485) (nat_lit 0) A10K2.u4708 from rfl, totK_node, atot4707, atot4708]
  decide +kernel

theorem arows4712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4712 = true := by
  rw [show A10K2.u4712 = KTree.node A10K2.u4710 (nat_lit 74340919) (nat_lit 1067621124) (nat_lit 0) A10K2.u4711 from rfl, allE_node, arows4710, irow4712, arows4711]
  all_goals rfl

theorem atot4712 : totK PA10K2 A10K2.u4712 = [0, 0, 467092711113, 3755196774306, 8044157351667, 5431022894303, 954657432020, 38593611784, 0, 0] := by
  rw [show A10K2.u4712 = KTree.node A10K2.u4710 (nat_lit 74340919) (nat_lit 1067621124) (nat_lit 0) A10K2.u4711 from rfl, totK_node, atot4710, atot4711]
  decide +kernel

theorem arows4717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4717 = true := by
  rw [show A10K2.u4717 = KTree.node A10K2.u4715 (nat_lit 74371398) (nat_lit 5376581670) (nat_lit 0) A10K2.u4716 from rfl, allE_node, arows4715, irow4717, arows4716]
  all_goals rfl

theorem atot4717 : totK PA10K2 A10K2.u4717 = [0, 0, 590805433127, 3125331024059, 6689112760916, 6334862481228, 2088942592919, 238342382240, 5982052406, 0] := by
  rw [show A10K2.u4717 = KTree.node A10K2.u4715 (nat_lit 74371398) (nat_lit 5376581670) (nat_lit 0) A10K2.u4716 from rfl, totK_node, atot4715, atot4716]
  decide +kernel

theorem arows4720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4720 = true := by
  rw [show A10K2.u4720 = KTree.node A10K2.u4718 (nat_lit 74398907) (nat_lit 7140223799) (nat_lit 0) A10K2.u4719 from rfl, allE_node, arows4718, irow4720, arows4719]
  all_goals rfl

theorem atot4720 : totK PA10K2 A10K2.u4720 = [0, 0, 1296531748355, 5840040908335, 8299817392268, 3964575556326, 588239631084, 25660650750, 0, 0] := by
  rw [show A10K2.u4720 = KTree.node A10K2.u4718 (nat_lit 74398907) (nat_lit 7140223799) (nat_lit 0) A10K2.u4719 from rfl, totK_node, atot4718, atot4719]
  decide +kernel

theorem arows4724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4724 = true := by
  rw [show A10K2.u4724 = KTree.node A10K2.u4722 (nat_lit 74451299) (nat_lit 8741311286) (nat_lit 0) A10K2.u4723 from rfl, allE_node, arows4722, irow4724, arows4723]
  all_goals rfl

theorem atot4724 : totK PA10K2 A10K2.u4724 = [0, 870591257894, 3748886101601, 6160595245818, 5331434726968, 2770713267168, 645752606465, 41590655314, 0, 0] := by
  rw [show A10K2.u4724 = KTree.node A10K2.u4722 (nat_lit 74451299) (nat_lit 8741311286) (nat_lit 0) A10K2.u4723 from rfl, totK_node, atot4722, atot4723]
  decide +kernel

theorem arows4727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4727 = true := by
  rw [show A10K2.u4727 = KTree.node A10K2.u4725 (nat_lit 74471436) (nat_lit 11759478708) (nat_lit 0) A10K2.u4726 from rfl, allE_node, arows4725, irow4727, arows4726]
  all_goals rfl

theorem atot4727 : totK PA10K2 A10K2.u4727 = [0, 668069535895, 4178323378322, 8025120389465, 5332300747804, 1052788444918, 44372202425, 0, 0, 0] := by
  rw [show A10K2.u4727 = KTree.node A10K2.u4725 (nat_lit 74471436) (nat_lit 11759478708) (nat_lit 0) A10K2.u4726 from rfl, totK_node, atot4725, atot4726]
  decide +kernel

theorem arows4735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4735 = true := by
  rw [show A10K2.u4735 = KTree.node A10K2.u4733 (nat_lit 74504341) (nat_lit 6840212376) (nat_lit 0) A10K2.u4734 from rfl, allE_node, arows4733, irow4735, arows4734]
  all_goals rfl

theorem atot4735 : totK PA10K2 A10K2.u4735 = [0, 836243354860, 3733750902821, 6611245891335, 5709174199958, 1933556074448, 223057316887, 5546304973, 0, 0] := by
  rw [show A10K2.u4735 = KTree.node A10K2.u4733 (nat_lit 74504341) (nat_lit 6840212376) (nat_lit 0) A10K2.u4734 from rfl, totK_node, atot4733, atot4734]
  decide +kernel

theorem arows4738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4738 = true := by
  rw [show A10K2.u4738 = KTree.node A10K2.u4736 (nat_lit 74532053) (nat_lit 6284350085) (nat_lit 0) A10K2.u4737 from rfl, allE_node, arows4736, irow4738, arows4737]
  all_goals rfl

theorem atot4738 : totK PA10K2 A10K2.u4738 = [0, 770689108024, 4442932025946, 8112195440954, 4926020055673, 812576341919, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4738 = KTree.node A10K2.u4736 (nat_lit 74532053) (nat_lit 6284350085) (nat_lit 0) A10K2.u4737 from rfl, totK_node, atot4736, atot4737]
  decide +kernel

theorem arows4742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4742 = true := by
  rw [show A10K2.u4742 = KTree.node A10K2.u4740 (nat_lit 74546574) (nat_lit 15177716178) (nat_lit 0) A10K2.u4741 from rfl, allE_node, arows4740, irow4742, arows4741]
  all_goals rfl

theorem atot4742 : totK PA10K2 A10K2.u4742 = [0, 554803763168, 3427259749847, 7474390470776, 6369177717563, 1665934142783, 87329600480, 0, 0, 0] := by
  rw [show A10K2.u4742 = KTree.node A10K2.u4740 (nat_lit 74546574) (nat_lit 15177716178) (nat_lit 0) A10K2.u4741 from rfl, totK_node, atot4740, atot4741]
  decide +kernel

theorem arows4745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4745 = true := by
  rw [show A10K2.u4745 = KTree.node A10K2.u4743 (nat_lit 74564961) (nat_lit 8212835464) (nat_lit 0) A10K2.u4744 from rfl, allE_node, arows4743, irow4745, arows4744]
  all_goals rfl

theorem atot4745 : totK PA10K2 A10K2.u4745 = [0, 0, 842946843809, 4519519752558, 7972293916384, 4639372819556, 811060017529, 37204059898, 0, 0] := by
  rw [show A10K2.u4745 = KTree.node A10K2.u4743 (nat_lit 74564961) (nat_lit 8212835464) (nat_lit 0) A10K2.u4744 from rfl, totK_node, atot4743, atot4744]
  decide +kernel

theorem arows4750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4750 = true := by
  rw [show A10K2.u4750 = KTree.node A10K2.u4748 (nat_lit 74582376) (nat_lit 9769282729) (nat_lit 0) A10K2.u4749 from rfl, allE_node, arows4748, irow4750, arows4749]
  all_goals rfl

theorem atot4750 : totK PA10K2 A10K2.u4750 = [0, 951328283053, 4408788716974, 7410360184643, 5159348633617, 1329160739002, 92022555445, 0, 0, 0] := by
  rw [show A10K2.u4750 = KTree.node A10K2.u4748 (nat_lit 74582376) (nat_lit 9769282729) (nat_lit 0) A10K2.u4749 from rfl, totK_node, atot4748, atot4749]
  decide +kernel

theorem arows4753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4753 = true := by
  rw [show A10K2.u4753 = KTree.node A10K2.u4751 (nat_lit 74594646) (nat_lit 9786733182) (nat_lit 0) A10K2.u4752 from rfl, allE_node, arows4751, irow4753, arows4752]
  all_goals rfl

theorem atot4753 : totK PA10K2 A10K2.u4753 = [0, 1303244906413, 5553697605369, 7697868914829, 3942717417313, 676314992264, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4753 = KTree.node A10K2.u4751 (nat_lit 74594646) (nat_lit 9786733182) (nat_lit 0) A10K2.u4752 from rfl, totK_node, atot4751, atot4752]
  decide +kernel

theorem arows4757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4757 = true := by
  rw [show A10K2.u4757 = KTree.node A10K2.u4755 (nat_lit 74614999) (nat_lit 7336475140) (nat_lit 0) A10K2.u4756 from rfl, allE_node, arows4755, irow4757, arows4756]
  all_goals rfl

theorem atot4757 : totK PA10K2 A10K2.u4757 = [0, 0, 2379631248810, 7923502038131, 7099502989459, 1608209758833, 77257018825, 0, 0, 0] := by
  rw [show A10K2.u4757 = KTree.node A10K2.u4755 (nat_lit 74614999) (nat_lit 7336475140) (nat_lit 0) A10K2.u4756 from rfl, totK_node, atot4755, atot4756]
  decide +kernel

theorem arows4760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4760 = true := by
  rw [show A10K2.u4760 = KTree.node A10K2.u4758 (nat_lit 74634431) (nat_lit 5400108768) (nat_lit 0) A10K2.u4759 from rfl, allE_node, arows4758, irow4760, arows4759]
  all_goals rfl

theorem atot4760 : totK PA10K2 A10K2.u4760 = [0, 0, 1591516679030, 6307655724703, 7712665597900, 2841819262339, 347703260918, 6354482628, 0, 0] := by
  rw [show A10K2.u4760 = KTree.node A10K2.u4758 (nat_lit 74634431) (nat_lit 5400108768) (nat_lit 0) A10K2.u4759 from rfl, totK_node, atot4758, atot4759]
  decide +kernel

theorem arows4766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4766 = true := by
  rw [show A10K2.u4766 = KTree.node A10K2.u4764 (nat_lit 74729123) (nat_lit 10521909316) (nat_lit 0) A10K2.u4765 from rfl, allE_node, arows4764, irow4766, arows4765]
  all_goals rfl

theorem atot4766 : totK PA10K2 A10K2.u4766 = [0, 0, 1051669300791, 5242084794773, 8334578039495, 3906850030624, 457446175333, 11801668502, 0, 0] := by
  rw [show A10K2.u4766 = KTree.node A10K2.u4764 (nat_lit 74729123) (nat_lit 10521909316) (nat_lit 0) A10K2.u4765 from rfl, totK_node, atot4764, atot4765]
  decide +kernel

theorem arows4769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4769 = true := by
  rw [show A10K2.u4769 = KTree.node A10K2.u4767 (nat_lit 74790738) (nat_lit 14635750634) (nat_lit 0) A10K2.u4768 from rfl, allE_node, arows4767, irow4769, arows4768]
  all_goals rfl

theorem atot4769 : totK PA10K2 A10K2.u4769 = [0, 0, 1221735548540, 5392666591906, 7785720101847, 3986194196229, 651079021303, 31452573850, 0, 0] := by
  rw [show A10K2.u4769 = KTree.node A10K2.u4767 (nat_lit 74790738) (nat_lit 14635750634) (nat_lit 0) A10K2.u4768 from rfl, totK_node, atot4767, atot4768]
  decide +kernel

theorem arows4773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4773 = true := by
  rw [show A10K2.u4773 = KTree.node A10K2.u4771 (nat_lit 74803126) (nat_lit 16799536538) (nat_lit 0) A10K2.u4772 from rfl, allE_node, arows4771, irow4773, arows4772]
  all_goals rfl

theorem atot4773 : totK PA10K2 A10K2.u4773 = [0, 0, 1041291455017, 5219537394217, 8324620251043, 4226816834168, 567439712729, 13317224979, 0, 0] := by
  rw [show A10K2.u4773 = KTree.node A10K2.u4771 (nat_lit 74803126) (nat_lit 16799536538) (nat_lit 0) A10K2.u4772 from rfl, totK_node, atot4771, atot4772]
  decide +kernel

theorem arows4776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4776 = true := by
  rw [show A10K2.u4776 = KTree.node A10K2.u4774 (nat_lit 74852141) (nat_lit 6535488372) (nat_lit 0) A10K2.u4775 from rfl, allE_node, arows4774, irow4776, arows4775]
  all_goals rfl

theorem atot4776 : totK PA10K2 A10K2.u4776 = [0, 0, 1039673314242, 5154995032003, 8141443984093, 4041784103336, 582497389023, 30429722018, 0, 0] := by
  rw [show A10K2.u4776 = KTree.node A10K2.u4774 (nat_lit 74852141) (nat_lit 6535488372) (nat_lit 0) A10K2.u4775 from rfl, totK_node, atot4774, atot4775]
  decide +kernel

theorem arows4781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4781 = true := by
  rw [show A10K2.u4781 = KTree.node A10K2.u4779 (nat_lit 74862632) (nat_lit 12782016780) (nat_lit 0) A10K2.u4780 from rfl, allE_node, arows4779, irow4781, arows4780]
  all_goals rfl

theorem atot4781 : totK PA10K2 A10K2.u4781 = [0, 0, 836002267270, 4591047513519, 8080361798610, 4469078239078, 686860952514, 17774690686, 0, 0] := by
  rw [show A10K2.u4781 = KTree.node A10K2.u4779 (nat_lit 74862632) (nat_lit 12782016780) (nat_lit 0) A10K2.u4780 from rfl, totK_node, atot4779, atot4780]
  decide +kernel

theorem arows4784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4784 = true := by
  rw [show A10K2.u4784 = KTree.node A10K2.u4782 (nat_lit 74892475) (nat_lit 7069627424) (nat_lit 0) A10K2.u4783 from rfl, allE_node, arows4782, irow4784, arows4783]
  all_goals rfl

theorem atot4784 : totK PA10K2 A10K2.u4784 = [0, 0, 0, 1673517959178, 6579234190716, 7457330024738, 2433661203860, 203573801850, 0, 0] := by
  rw [show A10K2.u4784 = KTree.node A10K2.u4782 (nat_lit 74892475) (nat_lit 7069627424) (nat_lit 0) A10K2.u4783 from rfl, totK_node, atot4782, atot4783]
  decide +kernel

theorem arows4788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4788 = true := by
  rw [show A10K2.u4788 = KTree.node A10K2.u4786 (nat_lit 75052388) (nat_lit 13494132798) (nat_lit 0) A10K2.u4787 from rfl, allE_node, arows4786, irow4788, arows4787]
  all_goals rfl

theorem atot4788 : totK PA10K2 A10K2.u4788 = [0, 1363867099552, 5514883778693, 7591896833782, 4018241106813, 685325248664, 149156773643, 86874954689, 6354482628, 0] := by
  rw [show A10K2.u4788 = KTree.node A10K2.u4786 (nat_lit 75052388) (nat_lit 13494132798) (nat_lit 0) A10K2.u4787 from rfl, totK_node, atot4786, atot4787]
  decide +kernel

theorem arows4791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4791 = true := by
  rw [show A10K2.u4791 = KTree.node A10K2.u4789 (nat_lit 75065270) (nat_lit 16799536538) (nat_lit 0) A10K2.u4790 from rfl, allE_node, arows4789, irow4791, arows4790]
  all_goals rfl

theorem atot4791 : totK PA10K2 A10K2.u4791 = [0, 843434427155, 4772524135230, 8420606480387, 5075266777765, 845605333695, 19530141922, 0, 0, 0] := by
  rw [show A10K2.u4791 = KTree.node A10K2.u4789 (nat_lit 75065270) (nat_lit 16799536538) (nat_lit 0) A10K2.u4790 from rfl, totK_node, atot4789, atot4790]
  decide +kernel

theorem arows4798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4798 = true := by
  rw [show A10K2.u4798 = KTree.node A10K2.u4796 (nat_lit 75084957) (nat_lit 6111184690) (nat_lit 0) A10K2.u4797 from rfl, allE_node, arows4796, irow4798, arows4797]
  all_goals rfl

theorem atot4798 : totK PA10K2 A10K2.u4798 = [0, 0, 1244016084325, 5429762667988, 7819052103121, 4041407014672, 677302338189, 31082886609, 0, 0] := by
  rw [show A10K2.u4798 = KTree.node A10K2.u4796 (nat_lit 75084957) (nat_lit 6111184690) (nat_lit 0) A10K2.u4797 from rfl, totK_node, atot4796, atot4797]
  decide +kernel

theorem arows4801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4801 = true := by
  rw [show A10K2.u4801 = KTree.node A10K2.u4799 (nat_lit 75097877) (nat_lit 6458549590) (nat_lit 0) A10K2.u4800 from rfl, allE_node, arows4799, irow4801, arows4800]
  all_goals rfl

theorem atot4801 : totK PA10K2 A10K2.u4801 = [0, 592431485893, 3122731773515, 6675639147359, 6617740308288, 2527364562749, 277968859250, 5885702948, 0, 0] := by
  rw [show A10K2.u4801 = KTree.node A10K2.u4799 (nat_lit 75097877) (nat_lit 6458549590) (nat_lit 0) A10K2.u4800 from rfl, totK_node, atot4799, atot4800]
  decide +kernel

theorem arows4805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4805 = true := by
  rw [show A10K2.u4805 = KTree.node A10K2.u4803 (nat_lit 75181266) (nat_lit 15577264525) (nat_lit 0) A10K2.u4804 from rfl, allE_node, arows4803, irow4805, arows4804]
  all_goals rfl

theorem atot4805 : totK PA10K2 A10K2.u4805 = [0, 1037688407184, 4800509160914, 7891574177889, 5024891635088, 998772912517, 43925276076, 0, 0, 0] := by
  rw [show A10K2.u4805 = KTree.node A10K2.u4803 (nat_lit 75181266) (nat_lit 15577264525) (nat_lit 0) A10K2.u4804 from rfl, totK_node, atot4803, atot4804]
  decide +kernel

theorem arows4808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4808 = true := by
  rw [show A10K2.u4808 = KTree.node A10K2.u4806 (nat_lit 75199368) (nat_lit 14170549419) (nat_lit 0) A10K2.u4807 from rfl, allE_node, arows4806, irow4808, arows4807]
  all_goals rfl

theorem atot4808 : totK PA10K2 A10K2.u4808 = [0, 613618390301, 3960924171211, 8031926178205, 5955110041167, 1431933094339, 75481680745, 0, 0, 0] := by
  rw [show A10K2.u4808 = KTree.node A10K2.u4806 (nat_lit 75199368) (nat_lit 14170549419) (nat_lit 0) A10K2.u4807 from rfl, totK_node, atot4806, atot4807]
  decide +kernel

theorem arows4813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4813 = true := by
  rw [show A10K2.u4813 = KTree.node A10K2.u4811 (nat_lit 75213027) (nat_lit 10391589043) (nat_lit 0) A10K2.u4812 from rfl, allE_node, arows4811, irow4813, arows4812]
  all_goals rfl

theorem atot4813 : totK PA10K2 A10K2.u4813 = [0, 0, 1006378738292, 5091577789241, 8410472857743, 4702558209084, 641645951321, 13679205470, 0, 0] := by
  rw [show A10K2.u4813 = KTree.node A10K2.u4811 (nat_lit 75213027) (nat_lit 10391589043) (nat_lit 0) A10K2.u4812 from rfl, totK_node, atot4811, atot4812]
  decide +kernel

theorem arows4816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4816 = true := by
  rw [show A10K2.u4816 = KTree.node A10K2.u4814 (nat_lit 75231780) (nat_lit 7998860419) (nat_lit 0) A10K2.u4815 from rfl, allE_node, arows4814, irow4816, arows4815]
  all_goals rfl

theorem atot4816 : totK PA10K2 A10K2.u4816 = [374610277362, 1242783310141, 2033550093555, 4193576463177, 6535310132110, 4369037126011, 991049596507, 61110126106, 0, 0] := by
  rw [show A10K2.u4816 = KTree.node A10K2.u4814 (nat_lit 75231780) (nat_lit 7998860419) (nat_lit 0) A10K2.u4815 from rfl, totK_node, atot4814, atot4815]
  decide +kernel

theorem arows4820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4820 = true := by
  rw [show A10K2.u4820 = KTree.node A10K2.u4818 (nat_lit 75504133) (nat_lit 6584847527) (nat_lit 0) A10K2.u4819 from rfl, allE_node, arows4818, irow4820, arows4819]
  all_goals rfl

theorem atot4820 : totK PA10K2 A10K2.u4820 = [1210095970834, 5399632423412, 7737025457865, 3931051428431, 644610851796, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4820 = KTree.node A10K2.u4818 (nat_lit 75504133) (nat_lit 6584847527) (nat_lit 0) A10K2.u4819 from rfl, totK_node, atot4818, atot4819]
  decide +kernel

theorem arows4823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4823 = true := by
  rw [show A10K2.u4823 = KTree.node A10K2.u4821 (nat_lit 75525575) (nat_lit 14506771514) (nat_lit 0) A10K2.u4822 from rfl, allE_node, arows4821, irow4823, arows4822]
  all_goals rfl

theorem atot4823 : totK PA10K2 A10K2.u4823 = [625789152892, 3983671715343, 8055961310468, 5751258076937, 1213058593724, 55909736440, 0, 0, 0, 0] := by
  rw [show A10K2.u4823 = KTree.node A10K2.u4821 (nat_lit 75525575) (nat_lit 14506771514) (nat_lit 0) A10K2.u4822 from rfl, totK_node, atot4821, atot4822]
  decide +kernel

theorem arows4829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4829 = true := by
  rw [show A10K2.u4829 = KTree.node A10K2.u4827 (nat_lit 75536545) (nat_lit 7964570272) (nat_lit 0) A10K2.u4828 from rfl, allE_node, arows4827, irow4829, arows4828]
  all_goals rfl

theorem atot4829 : totK PA10K2 A10K2.u4829 = [0, 1269830262893, 5585034691761, 7695165625339, 3613836072427, 612634129681, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4829 = KTree.node A10K2.u4827 (nat_lit 75536545) (nat_lit 7964570272) (nat_lit 0) A10K2.u4828 from rfl, totK_node, atot4827, atot4828]
  decide +kernel

theorem arows4832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4832 = true := by
  rw [show A10K2.u4832 = KTree.node A10K2.u4830 (nat_lit 75558395) (nat_lit 6202601874) (nat_lit 0) A10K2.u4831 from rfl, allE_node, arows4830, irow4832, arows4831]
  all_goals rfl

theorem atot4832 : totK PA10K2 A10K2.u4832 = [778776062315, 3616649110497, 6460907766948, 5927163927305, 2346678942010, 263104129908, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4832 = KTree.node A10K2.u4830 (nat_lit 75558395) (nat_lit 6202601874) (nat_lit 0) A10K2.u4831 from rfl, totK_node, atot4830, atot4831]
  decide +kernel

theorem arows4836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4836 = true := by
  rw [show A10K2.u4836 = KTree.node A10K2.u4834 (nat_lit 75639068) (nat_lit 12193009390) (nat_lit 0) A10K2.u4835 from rfl, allE_node, arows4834, irow4836, arows4835]
  all_goals rfl

theorem atot4836 : totK PA10K2 A10K2.u4836 = [937356224734, 4382364310248, 7545454798060, 5089691744410, 1097800115805, 62600422739, 0, 0, 0, 0] := by
  rw [show A10K2.u4836 = KTree.node A10K2.u4834 (nat_lit 75639068) (nat_lit 12193009390) (nat_lit 0) A10K2.u4835 from rfl, totK_node, atot4834, atot4835]
  decide +kernel

theorem arows4839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4839 = true := by
  rw [show A10K2.u4839 = KTree.node A10K2.u4837 (nat_lit 75651732) (nat_lit 12735388338) (nat_lit 0) A10K2.u4838 from rfl, allE_node, arows4837, irow4839, arows4838]
  all_goals rfl

theorem atot4839 : totK PA10K2 A10K2.u4839 = [441334865603, 3671471541775, 8045324886987, 5764800736988, 1144406460551, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u4839 = KTree.node A10K2.u4837 (nat_lit 75651732) (nat_lit 12735388338) (nat_lit 0) A10K2.u4838 from rfl, totK_node, atot4837, atot4838]
  decide +kernel

theorem arows4844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4844 = true := by
  rw [show A10K2.u4844 = KTree.node A10K2.u4842 (nat_lit 75679916) (nat_lit 13164463702) (nat_lit 0) A10K2.u4843 from rfl, allE_node, arows4842, irow4844, arows4843]
  all_goals rfl

theorem atot4844 : totK PA10K2 A10K2.u4844 = [306130628101, 2108650344977, 6005329241718, 7195417423396, 2804990219403, 348511603730, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4844 = KTree.node A10K2.u4842 (nat_lit 75679916) (nat_lit 13164463702) (nat_lit 0) A10K2.u4843 from rfl, totK_node, atot4842, atot4843]
  decide +kernel

theorem arows4847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4847 = true := by
  rw [show A10K2.u4847 = KTree.node A10K2.u4845 (nat_lit 75701098) (nat_lit 5456674763) (nat_lit 0) A10K2.u4846 from rfl, allE_node, arows4845, irow4847, arows4846]
  all_goals rfl

theorem atot4847 : totK PA10K2 A10K2.u4847 = [1058251235274, 5040580808652, 8099692936809, 4818873965320, 878813005508, 37664216019, 0, 0, 0, 0] := by
  rw [show A10K2.u4847 = KTree.node A10K2.u4845 (nat_lit 75701098) (nat_lit 5456674763) (nat_lit 0) A10K2.u4846 from rfl, totK_node, atot4845, atot4846]
  decide +kernel

theorem arows4851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4851 = true := by
  rw [show A10K2.u4851 = KTree.node A10K2.u4849 (nat_lit 75730446) (nat_lit 14579607298) (nat_lit 0) A10K2.u4850 from rfl, allE_node, arows4849, irow4851, arows4850]
  all_goals rfl

theorem atot4851 : totK PA10K2 A10K2.u4851 = [0, 1549899578389, 6218270699023, 8109527735009, 3541495285180, 415179371968, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4851 = KTree.node A10K2.u4849 (nat_lit 75730446) (nat_lit 14579607298) (nat_lit 0) A10K2.u4850 from rfl, totK_node, atot4849, atot4850]
  decide +kernel

theorem arows4854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4854 = true := by
  rw [show A10K2.u4854 = KTree.node A10K2.u4852 (nat_lit 75760120) (nat_lit 13324120295) (nat_lit 0) A10K2.u4853 from rfl, allE_node, arows4852, irow4854, arows4853]
  all_goals rfl

theorem atot4854 : totK PA10K2 A10K2.u4854 = [0, 963338091834, 4702569012721, 7700039301974, 4928732986228, 1153814473873, 80324158542, 0, 0, 0] := by
  rw [show A10K2.u4854 = KTree.node A10K2.u4852 (nat_lit 75760120) (nat_lit 13324120295) (nat_lit 0) A10K2.u4853 from rfl, totK_node, atot4852, atot4853]
  decide +kernel

theorem arows4863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4863 = true := by
  rw [show A10K2.u4863 = KTree.node A10K2.u4861 (nat_lit 75778372) (nat_lit 13109807505) (nat_lit 0) A10K2.u4862 from rfl, allE_node, arows4861, irow4863, arows4862]
  all_goals rfl

theorem atot4863 : totK PA10K2 A10K2.u4863 = [0, 1152506839773, 5362666960146, 8028694706486, 3887453607743, 488883051632, 11165512808, 0, 0, 0] := by
  rw [show A10K2.u4863 = KTree.node A10K2.u4861 (nat_lit 75778372) (nat_lit 13109807505) (nat_lit 0) A10K2.u4862 from rfl, totK_node, atot4861, atot4862]
  decide +kernel

theorem arows4866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4866 = true := by
  rw [show A10K2.u4866 = KTree.node A10K2.u4864 (nat_lit 75792830) (nat_lit 16077199309) (nat_lit 0) A10K2.u4865 from rfl, allE_node, arows4864, irow4866, arows4865]
  all_goals rfl

theorem atot4866 : totK PA10K2 A10K2.u4866 = [0, 218975725320, 2360221748548, 6683998844066, 6992045506875, 2635352988718, 424605762047, 25239774317, 0, 0] := by
  rw [show A10K2.u4866 = KTree.node A10K2.u4864 (nat_lit 75792830) (nat_lit 16077199309) (nat_lit 0) A10K2.u4865 from rfl, totK_node, atot4864, atot4865]
  decide +kernel

theorem arows4870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4870 = true := by
  rw [show A10K2.u4870 = KTree.node A10K2.u4868 (nat_lit 75811382) (nat_lit 10616191985) (nat_lit 0) A10K2.u4869 from rfl, allE_node, arows4868, irow4870, arows4869]
  all_goals rfl

theorem atot4870 : totK PA10K2 A10K2.u4870 = [0, 0, 1363336057817, 5785167604444, 7725235809781, 3275383584296, 428716781497, 10894784572, 0, 0] := by
  rw [show A10K2.u4870 = KTree.node A10K2.u4868 (nat_lit 75811382) (nat_lit 10616191985) (nat_lit 0) A10K2.u4869 from rfl, totK_node, atot4868, atot4869]
  decide +kernel

theorem arows4873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4873 = true := by
  rw [show A10K2.u4873 = KTree.node A10K2.u4871 (nat_lit 75895069) (nat_lit 5953473476) (nat_lit 0) A10K2.u4872 from rfl, allE_node, arows4871, irow4873, arows4872]
  all_goals rfl

theorem atot4873 : totK PA10K2 A10K2.u4873 = [0, 1336795214440, 5269875505133, 7395302731490, 4337567372865, 955516052451, 59842360860, 0, 0, 0] := by
  rw [show A10K2.u4873 = KTree.node A10K2.u4871 (nat_lit 75895069) (nat_lit 5953473476) (nat_lit 0) A10K2.u4872 from rfl, totK_node, atot4871, atot4872]
  decide +kernel

theorem arows4878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4878 = true := by
  rw [show A10K2.u4878 = KTree.node A10K2.u4876 (nat_lit 75908833) (nat_lit 4074957632) (nat_lit 0) A10K2.u4877 from rfl, allE_node, arows4876, irow4878, arows4877]
  all_goals rfl

theorem atot4878 : totK PA10K2 A10K2.u4878 = [0, 819545818442, 4893294080593, 8295653202620, 4204594995824, 554883237585, 12388698189, 0, 0, 0] := by
  rw [show A10K2.u4878 = KTree.node A10K2.u4876 (nat_lit 75908833) (nat_lit 4074957632) (nat_lit 0) A10K2.u4877 from rfl, totK_node, atot4876, atot4877]
  decide +kernel

theorem arows4881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4881 = true := by
  rw [show A10K2.u4881 = KTree.node A10K2.u4879 (nat_lit 75934354) (nat_lit 15529038244) (nat_lit 0) A10K2.u4880 from rfl, allE_node, arows4879, irow4881, arows4880]
  all_goals rfl

theorem atot4881 : totK PA10K2 A10K2.u4881 = [0, 0, 1963462539334, 7393579584398, 7515436632708, 1889631460524, 107556580210, 0, 0, 0] := by
  rw [show A10K2.u4881 = KTree.node A10K2.u4879 (nat_lit 75934354) (nat_lit 15529038244) (nat_lit 0) A10K2.u4880 from rfl, totK_node, atot4879, atot4880]
  decide +kernel

theorem arows4885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4885 = true := by
  rw [show A10K2.u4885 = KTree.node A10K2.u4883 (nat_lit 75959884) (nat_lit 8264386543) (nat_lit 0) A10K2.u4884 from rfl, allE_node, arows4883, irow4885, arows4884]
  all_goals rfl

theorem atot4885 : totK PA10K2 A10K2.u4885 = [0, 1223096654933, 4974046018799, 7131070774999, 4457377092928, 1406918528262, 185475499233, 5676195732, 0, 0] := by
  rw [show A10K2.u4885 = KTree.node A10K2.u4883 (nat_lit 75959884) (nat_lit 8264386543) (nat_lit 0) A10K2.u4884 from rfl, totK_node, atot4883, atot4884]
  decide +kernel

theorem arows4888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4888 = true := by
  rw [show A10K2.u4888 = KTree.node A10K2.u4886 (nat_lit 76096979) (nat_lit 10649282280) (nat_lit 0) A10K2.u4887 from rfl, allE_node, arows4886, irow4888, arows4887]
  all_goals rfl

theorem atot4888 : totK PA10K2 A10K2.u4888 = [848323660542, 3547381174858, 5791375605354, 5437044546079, 3273176294559, 837609882760, 55990884373, 0, 0, 0] := by
  rw [show A10K2.u4888 = KTree.node A10K2.u4886 (nat_lit 76096979) (nat_lit 10649282280) (nat_lit 0) A10K2.u4887 from rfl, totK_node, atot4886, atot4887]
  decide +kernel

theorem arows4894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4894 = true := by
  rw [show A10K2.u4894 = KTree.node A10K2.u4892 (nat_lit 76105915) (nat_lit 6901297462) (nat_lit 0) A10K2.u4893 from rfl, allE_node, arows4892, irow4894, arows4893]
  all_goals rfl

theorem atot4894 : totK PA10K2 A10K2.u4894 = [1116151991747, 5166504769268, 7935714133402, 4273298834258, 633314436429, 17782321361, 0, 0, 0, 0] := by
  rw [show A10K2.u4894 = KTree.node A10K2.u4892 (nat_lit 76105915) (nat_lit 6901297462) (nat_lit 0) A10K2.u4893 from rfl, totK_node, atot4892, atot4893]
  decide +kernel

theorem arows4897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4897 = true := by
  rw [show A10K2.u4897 = KTree.node A10K2.u4895 (nat_lit 76129464) (nat_lit 9314152661) (nat_lit 0) A10K2.u4896 from rfl, allE_node, arows4895, irow4897, arows4896]
  all_goals rfl

theorem atot4897 : totK PA10K2 A10K2.u4897 = [260403760671, 2611672877934, 7265323925499, 7200897814285, 2235557654399, 150806749985, 0, 0, 0, 0] := by
  rw [show A10K2.u4897 = KTree.node A10K2.u4895 (nat_lit 76129464) (nat_lit 9314152661) (nat_lit 0) A10K2.u4896 from rfl, totK_node, atot4895, atot4896]
  decide +kernel

theorem arows4901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4901 = true := by
  rw [show A10K2.u4901 = KTree.node A10K2.u4899 (nat_lit 76138536) (nat_lit 11758837009) (nat_lit 0) A10K2.u4900 from rfl, allE_node, arows4899, irow4901, arows4900]
  all_goals rfl

theorem atot4901 : totK PA10K2 A10K2.u4901 = [0, 1113607834297, 5070909596270, 7701959316752, 4205374164438, 754524428935, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4901 = KTree.node A10K2.u4899 (nat_lit 76138536) (nat_lit 11758837009) (nat_lit 0) A10K2.u4900 from rfl, totK_node, atot4899, atot4900]
  decide +kernel

theorem arows4904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4904 = true := by
  rw [show A10K2.u4904 = KTree.node A10K2.u4902 (nat_lit 76157004) (nat_lit 10725755786) (nat_lit 0) A10K2.u4903 from rfl, allE_node, arows4902, irow4904, arows4903]
  all_goals rfl

theorem atot4904 : totK PA10K2 A10K2.u4904 = [1141181548011, 4837136267232, 7170990171192, 4705199224464, 1314023610855, 100610308258, 0, 0, 0, 0] := by
  rw [show A10K2.u4904 = KTree.node A10K2.u4902 (nat_lit 76157004) (nat_lit 10725755786) (nat_lit 0) A10K2.u4903 from rfl, totK_node, atot4902, atot4903]
  decide +kernel

theorem arows4909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4909 = true := by
  rw [show A10K2.u4909 = KTree.node A10K2.u4907 (nat_lit 76169313) (nat_lit 9996329722) (nat_lit 0) A10K2.u4908 from rfl, allE_node, arows4907, irow4909, arows4908]
  all_goals rfl

theorem atot4909 : totK PA10K2 A10K2.u4909 = [1017553662282, 5029832906269, 7977456051105, 4433933790396, 729453050569, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4909 = KTree.node A10K2.u4907 (nat_lit 76169313) (nat_lit 9996329722) (nat_lit 0) A10K2.u4908 from rfl, totK_node, atot4907, atot4908]
  decide +kernel

theorem arows4912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4912 = true := by
  rw [show A10K2.u4912 = KTree.node A10K2.u4910 (nat_lit 76195159) (nat_lit 6118585603) (nat_lit 0) A10K2.u4911 from rfl, allE_node, arows4910, irow4912, arows4911]
  all_goals rfl

theorem atot4912 : totK PA10K2 A10K2.u4912 = [0, 2163216585842, 7559848755383, 7385961759189, 1876536042001, 102420466534, 0, 0, 0, 0] := by
  rw [show A10K2.u4912 = KTree.node A10K2.u4910 (nat_lit 76195159) (nat_lit 6118585603) (nat_lit 0) A10K2.u4911 from rfl, totK_node, atot4910, atot4911]
  decide +kernel

theorem arows4916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4916 = true := by
  rw [show A10K2.u4916 = KTree.node A10K2.u4914 (nat_lit 76208997) (nat_lit 7244284449) (nat_lit 0) A10K2.u4915 from rfl, allE_node, arows4914, irow4916, arows4915]
  all_goals rfl

theorem atot4916 : totK PA10K2 A10K2.u4916 = [773889436601, 3528245873549, 6561514840150, 5954350542987, 2175620619422, 291306829918, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4916 = KTree.node A10K2.u4914 (nat_lit 76208997) (nat_lit 7244284449) (nat_lit 0) A10K2.u4915 from rfl, totK_node, atot4914, atot4915]
  decide +kernel

theorem arows4919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4919 = true := by
  rw [show A10K2.u4919 = KTree.node A10K2.u4917 (nat_lit 76246967) (nat_lit 15196976937) (nat_lit 0) A10K2.u4918 from rfl, allE_node, arows4917, irow4919, arows4918]
  all_goals rfl

theorem atot4919 : totK PA10K2 A10K2.u4919 = [595724520244, 3688831700477, 7770243575207, 6307970237277, 1680390755784, 113795990376, 0, 0, 0, 0] := by
  rw [show A10K2.u4919 = KTree.node A10K2.u4917 (nat_lit 76246967) (nat_lit 15196976937) (nat_lit 0) A10K2.u4918 from rfl, totK_node, atot4917, atot4918]
  decide +kernel

theorem arows4926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4926 = true := by
  rw [show A10K2.u4926 = KTree.node A10K2.u4924 (nat_lit 76277121) (nat_lit 7040825791) (nat_lit 0) A10K2.u4925 from rfl, allE_node, arows4924, irow4926, arows4925]
  all_goals rfl

theorem atot4926 : totK PA10K2 A10K2.u4926 = [0, 932636842700, 4927733340512, 8355822642480, 4998306031835, 813758490496, 18957482694, 0, 0, 0] := by
  rw [show A10K2.u4926 = KTree.node A10K2.u4924 (nat_lit 76277121) (nat_lit 7040825791) (nat_lit 0) A10K2.u4925 from rfl, totK_node, atot4924, atot4925]
  decide +kernel

theorem arows4929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4929 = true := by
  rw [show A10K2.u4929 = KTree.node A10K2.u4927 (nat_lit 76362972) (nat_lit 11041814247) (nat_lit 0) A10K2.u4928 from rfl, allE_node, arows4927, irow4929, arows4928]
  all_goals rfl

theorem atot4929 : totK PA10K2 A10K2.u4929 = [0, 1307696148768, 5364775803710, 7375615868674, 4111569151142, 950181966228, 74901459239, 0, 0, 0] := by
  rw [show A10K2.u4929 = KTree.node A10K2.u4927 (nat_lit 76362972) (nat_lit 11041814247) (nat_lit 0) A10K2.u4928 from rfl, totK_node, atot4927, atot4928]
  decide +kernel

theorem arows4933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4933 = true := by
  rw [show A10K2.u4933 = KTree.node A10K2.u4931 (nat_lit 76375223) (nat_lit 14583484606) (nat_lit 0) A10K2.u4932 from rfl, allE_node, arows4931, irow4933, arows4932]
  all_goals rfl

theorem atot4933 : totK PA10K2 A10K2.u4933 = [0, 912923523059, 4962549205929, 8416383906483, 4566097254891, 631344895261, 13202416085, 0, 0, 0] := by
  rw [show A10K2.u4933 = KTree.node A10K2.u4931 (nat_lit 76375223) (nat_lit 14583484606) (nat_lit 0) A10K2.u4932 from rfl, totK_node, atot4931, atot4932]
  decide +kernel

theorem arows4936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4936 = true := by
  rw [show A10K2.u4936 = KTree.node A10K2.u4934 (nat_lit 76394487) (nat_lit 14202965093) (nat_lit 0) A10K2.u4935 from rfl, allE_node, arows4934, irow4936, arows4935]
  all_goals rfl

theorem atot4936 : totK PA10K2 A10K2.u4936 = [0, 0, 1297331453768, 5588746442715, 7664910591892, 3709642121590, 627114246129, 31018567651, 0, 0] := by
  rw [show A10K2.u4936 = KTree.node A10K2.u4934 (nat_lit 76394487) (nat_lit 14202965093) (nat_lit 0) A10K2.u4935 from rfl, totK_node, atot4934, atot4935]
  decide +kernel

theorem arows4941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4941 = true := by
  rw [show A10K2.u4941 = KTree.node A10K2.u4939 (nat_lit 76408097) (nat_lit 3996545355) (nat_lit 0) A10K2.u4940 from rfl, allE_node, arows4939, irow4941, arows4940]
  all_goals rfl

theorem atot4941 : totK PA10K2 A10K2.u4941 = [0, 556222090703, 2930552580315, 6222400398910, 6537616505724, 2553595855792, 278009379093, 5685526223, 0, 0] := by
  rw [show A10K2.u4941 = KTree.node A10K2.u4939 (nat_lit 76408097) (nat_lit 3996545355) (nat_lit 0) A10K2.u4940 from rfl, totK_node, atot4939, atot4940]
  decide +kernel

theorem arows4944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4944 = true := by
  rw [show A10K2.u4944 = KTree.node A10K2.u4942 (nat_lit 76426395) (nat_lit 9975195466) (nat_lit 0) A10K2.u4943 from rfl, allE_node, arows4942, irow4944, arows4943]
  all_goals rfl

theorem atot4944 : totK PA10K2 A10K2.u4944 = [0, 1018573260006, 4746106565924, 7828122952900, 4726967782542, 828412322246, 37229241746, 0, 0, 0] := by
  rw [show A10K2.u4944 = KTree.node A10K2.u4942 (nat_lit 76426395) (nat_lit 9975195466) (nat_lit 0) A10K2.u4943 from rfl, totK_node, atot4942, atot4943]
  decide +kernel

theorem arows4948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4948 = true := by
  rw [show A10K2.u4948 = KTree.node A10K2.u4946 (nat_lit 76437518) (nat_lit 8819482308) (nat_lit 0) A10K2.u4947 from rfl, allE_node, arows4946, irow4948, arows4947]
  all_goals rfl

theorem atot4948 : totK PA10K2 A10K2.u4948 = [0, 583209941258, 4081055921669, 8171193250297, 5159469206005, 863114066510, 33066034854, 0, 0, 0] := by
  rw [show A10K2.u4948 = KTree.node A10K2.u4946 (nat_lit 76437518) (nat_lit 8819482308) (nat_lit 0) A10K2.u4947 from rfl, totK_node, atot4946, atot4947]
  decide +kernel

theorem arows4951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4951 = true := by
  rw [show A10K2.u4951 = KTree.node A10K2.u4949 (nat_lit 76466003) (nat_lit 10041449714) (nat_lit 0) A10K2.u4950 from rfl, allE_node, arows4949, irow4951, arows4950]
  all_goals rfl

theorem atot4951 : totK PA10K2 A10K2.u4951 = [0, 305746175225, 2131245511605, 6184781178370, 7347074956830, 2528579040030, 269629529381, 6239673734, 0, 0] := by
  rw [show A10K2.u4951 = KTree.node A10K2.u4949 (nat_lit 76466003) (nat_lit 10041449714) (nat_lit 0) A10K2.u4950 from rfl, totK_node, atot4949, atot4950]
  decide +kernel

theorem arows4957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4957 = true := by
  rw [show A10K2.u4957 = KTree.node A10K2.u4955 (nat_lit 76495187) (nat_lit 10390678949) (nat_lit 0) A10K2.u4956 from rfl, allE_node, arows4955, irow4957, arows4956]
  all_goals rfl

theorem atot4957 : totK PA10K2 A10K2.u4957 = [0, 1059841905936, 5210062490119, 8334048273828, 4590118711157, 745609197338, 31285368086, 0, 0, 0] := by
  rw [show A10K2.u4957 = KTree.node A10K2.u4955 (nat_lit 76495187) (nat_lit 10390678949) (nat_lit 0) A10K2.u4956 from rfl, totK_node, atot4955, atot4956]
  decide +kernel

theorem arows4960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4960 = true := by
  rw [show A10K2.u4960 = KTree.node A10K2.u4958 (nat_lit 76548948) (nat_lit 12650956078) (nat_lit 0) A10K2.u4959 from rfl, allE_node, arows4958, irow4960, arows4959]
  all_goals rfl

theorem atot4960 : totK PA10K2 A10K2.u4960 = [912565010242, 3956057003451, 6238466017572, 4795914042788, 2540180040741, 763119756891, 56100664475, 0, 0, 0] := by
  rw [show A10K2.u4960 = KTree.node A10K2.u4958 (nat_lit 76548948) (nat_lit 12650956078) (nat_lit 0) A10K2.u4959 from rfl, totK_node, atot4958, atot4959]
  decide +kernel

theorem arows4964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4964 = true := by
  rw [show A10K2.u4964 = KTree.node A10K2.u4962 (nat_lit 76567912) (nat_lit 8858531524) (nat_lit 0) A10K2.u4963 from rfl, allE_node, arows4962, irow4964, arows4963]
  all_goals rfl

theorem atot4964 : totK PA10K2 A10K2.u4964 = [1132860514623, 5344375498164, 8104663787654, 4106917494274, 586288135587, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u4964 = KTree.node A10K2.u4962 (nat_lit 76567912) (nat_lit 8858531524) (nat_lit 0) A10K2.u4963 from rfl, totK_node, atot4962, atot4963]
  decide +kernel

theorem arows4967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4967 = true := by
  rw [show A10K2.u4967 = KTree.node A10K2.u4965 (nat_lit 76582839) (nat_lit 15155692245) (nat_lit 0) A10K2.u4966 from rfl, allE_node, arows4965, irow4967, arows4966]
  all_goals rfl

theorem atot4967 : totK PA10K2 A10K2.u4967 = [0, 1304671909131, 5476480762266, 7673855204927, 3790503274646, 644000511428, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4967 = KTree.node A10K2.u4965 (nat_lit 76582839) (nat_lit 15155692245) (nat_lit 0) A10K2.u4966 from rfl, totK_node, atot4965, atot4966]
  decide +kernel

theorem arows4972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4972 = true := by
  rw [show A10K2.u4972 = KTree.node A10K2.u4970 (nat_lit 76603506) (nat_lit 8149957107) (nat_lit 0) A10K2.u4971 from rfl, allE_node, arows4970, irow4972, arows4971]
  all_goals rfl

theorem atot4972 : totK PA10K2 A10K2.u4972 = [622048478734, 3117646434301, 6440826936071, 6359595962184, 2381283627174, 263491127832, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4972 = KTree.node A10K2.u4970 (nat_lit 76603506) (nat_lit 8149957107) (nat_lit 0) A10K2.u4971 from rfl, totK_node, atot4970, atot4971]
  decide +kernel

theorem arows4975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4975 = true := by
  rw [show A10K2.u4975 = KTree.node A10K2.u4973 (nat_lit 76628238) (nat_lit 8838998377) (nat_lit 0) A10K2.u4974 from rfl, allE_node, arows4973, irow4975, arows4974]
  all_goals rfl

theorem atot4975 : totK PA10K2 A10K2.u4975 = [958036616463, 4939426197412, 8002179518998, 4510563171257, 728837505326, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4975 = KTree.node A10K2.u4973 (nat_lit 76628238) (nat_lit 8838998377) (nat_lit 0) A10K2.u4974 from rfl, totK_node, atot4973, atot4974]
  decide +kernel

theorem arows4979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4979 = true := by
  rw [show A10K2.u4979 = KTree.node A10K2.u4977 (nat_lit 76642239) (nat_lit 14162250694) (nat_lit 0) A10K2.u4978 from rfl, allE_node, arows4977, irow4979, arows4978]
  all_goals rfl

theorem atot4979 : totK PA10K2 A10K2.u4979 = [461607179050, 3205206191635, 7544359518451, 6456984967448, 1646144722447, 89921577226, 0, 0, 0, 0] := by
  rw [show A10K2.u4979 = KTree.node A10K2.u4977 (nat_lit 76642239) (nat_lit 14162250694) (nat_lit 0) A10K2.u4978 from rfl, totK_node, atot4977, atot4978]
  decide +kernel

theorem arows4982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4982 = true := by
  rw [show A10K2.u4982 = KTree.node A10K2.u4980 (nat_lit 76662167) (nat_lit 13154720955) (nat_lit 0) A10K2.u4981 from rfl, allE_node, arows4980, irow4982, arows4981]
  all_goals rfl

theorem atot4982 : totK PA10K2 A10K2.u4982 = [0, 882389862906, 4560459299750, 7914348651873, 4647817259608, 815251993776, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4982 = KTree.node A10K2.u4980 (nat_lit 76662167) (nat_lit 13154720955) (nat_lit 0) A10K2.u4981 from rfl, totK_node, atot4980, atot4981]
  decide +kernel

theorem arows4990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4990 = true := by
  rw [show A10K2.u4990 = KTree.node A10K2.u4988 (nat_lit 76679968) (nat_lit 12740398072) (nat_lit 0) A10K2.u4989 from rfl, allE_node, arows4988, irow4990, arows4989]
  all_goals rfl

theorem atot4990 : totK PA10K2 A10K2.u4990 = [1037230194623, 4450897866357, 7294508463888, 5064777380271, 1300270989627, 95040550853, 0, 0, 0, 0] := by
  rw [show A10K2.u4990 = KTree.node A10K2.u4988 (nat_lit 76679968) (nat_lit 12740398072) (nat_lit 0) A10K2.u4989 from rfl, totK_node, atot4988, atot4989]
  decide +kernel

theorem arows4993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4993 = true := by
  rw [show A10K2.u4993 = KTree.node A10K2.u4991 (nat_lit 76691668) (nat_lit 11753543645) (nat_lit 0) A10K2.u4992 from rfl, allE_node, arows4991, irow4993, arows4992]
  all_goals rfl

theorem atot4993 : totK PA10K2 A10K2.u4993 = [1306602522148, 5487331008792, 7682132221640, 3989210508400, 681361909673, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4993 = KTree.node A10K2.u4991 (nat_lit 76691668) (nat_lit 11753543645) (nat_lit 0) A10K2.u4992 from rfl, totK_node, atot4991, atot4992]
  decide +kernel

theorem arows4997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4997 = true := by
  rw [show A10K2.u4997 = KTree.node A10K2.u4995 (nat_lit 76710791) (nat_lit 13290338082) (nat_lit 0) A10K2.u4996 from rfl, allE_node, arows4995, irow4997, arows4996]
  all_goals rfl

theorem atot4997 : totK PA10K2 A10K2.u4997 = [0, 2573365758941, 8041892913779, 6839579447993, 1531824012670, 71254002758, 0, 0, 0, 0] := by
  rw [show A10K2.u4997 = KTree.node A10K2.u4995 (nat_lit 76710791) (nat_lit 13290338082) (nat_lit 0) A10K2.u4996 from rfl, totK_node, atot4995, atot4996]
  decide +kernel

theorem arows5000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5000 = true := by
  rw [show A10K2.u5000 = KTree.node A10K2.u4998 (nat_lit 76729118) (nat_lit 7082995048) (nat_lit 0) A10K2.u4999 from rfl, allE_node, arows4998, irow5000, arows4999]
  all_goals rfl

theorem atot5000 : totK PA10K2 A10K2.u5000 = [0, 1556922620683, 6185742853125, 7825190323556, 2989560411922, 354954660074, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5000 = KTree.node A10K2.u4998 (nat_lit 76729118) (nat_lit 7082995048) (nat_lit 0) A10K2.u4999 from rfl, totK_node, atot4998, atot4999]
  decide +kernel

theorem arows5005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5005 = true := by
  rw [show A10K2.u5005 = KTree.node A10K2.u5003 (nat_lit 76815474) (nat_lit 8294005189) (nat_lit 0) A10K2.u5004 from rfl, allE_node, arows5003, irow5005, arows5004]
  all_goals rfl

theorem atot5005 : totK PA10K2 A10K2.u5005 = [0, 1042302570321, 5163809019349, 7925911793715, 4088528646430, 657936914545, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u5005 = KTree.node A10K2.u5003 (nat_lit 76815474) (nat_lit 8294005189) (nat_lit 0) A10K2.u5004 from rfl, totK_node, atot5003, atot5004]
  decide +kernel

theorem arows5008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5008 = true := by
  rw [show A10K2.u5008 = KTree.node A10K2.u5006 (nat_lit 76837278) (nat_lit 10428440417) (nat_lit 0) A10K2.u5007 from rfl, allE_node, arows5006, irow5008, arows5007]
  all_goals rfl

theorem atot5008 : totK PA10K2 A10K2.u5008 = [0, 1261759934612, 5478935784817, 7914671648100, 4031689621337, 602046421759, 13207830636, 0, 0, 0] := by
  rw [show A10K2.u5008 = KTree.node A10K2.u5006 (nat_lit 76837278) (nat_lit 10428440417) (nat_lit 0) A10K2.u5007 from rfl, totK_node, atot5006, atot5007]
  decide +kernel

theorem arows5012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5012 = true := by
  rw [show A10K2.u5012 = KTree.node A10K2.u5010 (nat_lit 76891321) (nat_lit 1708266121) (nat_lit 0) A10K2.u5011 from rfl, allE_node, arows5010, irow5012, arows5011]
  all_goals rfl

theorem atot5012 : totK PA10K2 A10K2.u5012 = [0, 784966291201, 4516910234865, 8116314086296, 4745797880655, 767246377453, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u5012 = KTree.node A10K2.u5010 (nat_lit 76891321) (nat_lit 1708266121) (nat_lit 0) A10K2.u5011 from rfl, totK_node, atot5010, atot5011]
  decide +kernel

theorem arows5015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5015 = true := by
  rw [show A10K2.u5015 = KTree.node A10K2.u5013 (nat_lit 76939541) (nat_lit 6796925496) (nat_lit 0) A10K2.u5014 from rfl, allE_node, arows5013, irow5015, arows5014]
  all_goals rfl

theorem atot5015 : totK PA10K2 A10K2.u5015 = [0, 1203290571222, 5245125466812, 7713110536897, 4266898476412, 794685200433, 37931615632, 0, 0, 0] := by
  rw [show A10K2.u5015 = KTree.node A10K2.u5013 (nat_lit 76939541) (nat_lit 6796925496) (nat_lit 0) A10K2.u5014 from rfl, totK_node, atot5013, atot5014]
  decide +kernel

theorem arows5021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5021 = true := by
  rw [show A10K2.u5021 = KTree.node A10K2.u5019 (nat_lit 76951255) (nat_lit 11669929475) (nat_lit 0) A10K2.u5020 from rfl, allE_node, arows5019, irow5021, arows5020]
  all_goals rfl

theorem atot5021 : totK PA10K2 A10K2.u5021 = [0, 1122718298380, 4959476254484, 7721855812572, 4346271550913, 708641683747, 36463937579, 0, 0, 0] := by
  rw [show A10K2.u5021 = KTree.node A10K2.u5019 (nat_lit 76951255) (nat_lit 11669929475) (nat_lit 0) A10K2.u5020 from rfl, totK_node, atot5019, atot5020]
  decide +kernel

theorem arows5024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5024 = true := by
  rw [show A10K2.u5024 = KTree.node A10K2.u5022 (nat_lit 76962147) (nat_lit 9194853334) (nat_lit 0) A10K2.u5023 from rfl, allE_node, arows5022, irow5024, arows5023]
  all_goals rfl

theorem atot5024 : totK PA10K2 A10K2.u5024 = [0, 474214578890, 3793377971073, 8055318769761, 5361426772982, 1016198281550, 57372072225, 0, 0, 0] := by
  rw [show A10K2.u5024 = KTree.node A10K2.u5022 (nat_lit 76962147) (nat_lit 9194853334) (nat_lit 0) A10K2.u5023 from rfl, totK_node, atot5022, atot5023]
  decide +kernel

theorem arows5028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5028 = true := by
  rw [show A10K2.u5028 = KTree.node A10K2.u5026 (nat_lit 76990564) (nat_lit 13600911956) (nat_lit 0) A10K2.u5027 from rfl, allE_node, arows5026, irow5028, arows5027]
  all_goals rfl

theorem atot5028 : totK PA10K2 A10K2.u5028 = [0, 319364639558, 2262895294516, 6215376349933, 6868760556340, 2577730356427, 327590491638, 6354482628, 0, 0] := by
  rw [show A10K2.u5028 = KTree.node A10K2.u5026 (nat_lit 76990564) (nat_lit 13600911956) (nat_lit 0) A10K2.u5027 from rfl, totK_node, atot5026, atot5027]
  decide +kernel

theorem arows5031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5031 = true := by
  rw [show A10K2.u5031 = KTree.node A10K2.u5029 (nat_lit 77600916) (nat_lit 12124513404) (nat_lit 0) A10K2.u5030 from rfl, allE_node, arows5029, irow5031, arows5030]
  all_goals rfl

theorem atot5031 : totK PA10K2 A10K2.u5031 = [0, 1272138273808, 5412915018667, 7662485164895, 3941908124989, 648464328581, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5031 = KTree.node A10K2.u5029 (nat_lit 77600916) (nat_lit 12124513404) (nat_lit 0) A10K2.u5030 from rfl, totK_node, atot5029, atot5030]
  decide +kernel

theorem arows5036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5036 = true := by
  rw [show A10K2.u5036 = KTree.node A10K2.u5034 (nat_lit 77622328) (nat_lit 14679186370) (nat_lit 0) A10K2.u5035 from rfl, allE_node, arows5034, irow5036, arows5035]
  all_goals rfl

theorem atot5036 : totK PA10K2 A10K2.u5036 = [0, 625789152892, 4136478979509, 8202226125799, 5444535903888, 1105908831118, 47212543301, 0, 0, 0] := by
  rw [show A10K2.u5036 = KTree.node A10K2.u5034 (nat_lit 77622328) (nat_lit 14679186370) (nat_lit 0) A10K2.u5035 from rfl, totK_node, atot5034, atot5035]
  decide +kernel

theorem arows5039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5039 = true := by
  rw [show A10K2.u5039 = KTree.node A10K2.u5037 (nat_lit 77632389) (nat_lit 5047026404) (nat_lit 0) A10K2.u5038 from rfl, allE_node, arows5037, irow5039, arows5038]
  all_goals rfl

theorem atot5039 : totK PA10K2 A10K2.u5039 = [0, 0, 1325564329948, 5607535831774, 7668798166047, 3607182155352, 612138080085, 30650496230, 0, 0] := by
  rw [show A10K2.u5039 = KTree.node A10K2.u5037 (nat_lit 77632389) (nat_lit 5047026404) (nat_lit 0) A10K2.u5038 from rfl, totK_node, atot5037, atot5038]
  decide +kernel

theorem arows5043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5043 = true := by
  rw [show A10K2.u5043 = KTree.node A10K2.u5041 (nat_lit 77655219) (nat_lit 7420897762) (nat_lit 0) A10K2.u5042 from rfl, allE_node, arows5041, irow5043, arows5042]
  all_goals rfl

theorem atot5043 : totK PA10K2 A10K2.u5043 = [0, 778776062315, 3463141451006, 6420903333219, 6126000519782, 2319863769445, 248877833895, 5546304973, 0, 0] := by
  rw [show A10K2.u5043 = KTree.node A10K2.u5041 (nat_lit 77655219) (nat_lit 7420897762) (nat_lit 0) A10K2.u5042 from rfl, totK_node, atot5041, atot5042]
  decide +kernel

theorem arows5046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5046 = true := by
  rw [show A10K2.u5046 = KTree.node A10K2.u5044 (nat_lit 77736100) (nat_lit 13604907954) (nat_lit 0) A10K2.u5045 from rfl, allE_node, arows5044, irow5046, arows5045]
  all_goals rfl

theorem atot5046 : totK PA10K2 A10K2.u5046 = [0, 833355721226, 4279109816105, 7677148571003, 5117146066255, 1055808027731, 62165360546, 0, 0, 0] := by
  rw [show A10K2.u5046 = KTree.node A10K2.u5044 (nat_lit 77736100) (nat_lit 13604907954) (nat_lit 0) A10K2.u5045 from rfl, totK_node, atot5044, atot5045]
  decide +kernel

theorem arows5053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5053 = true := by
  rw [show A10K2.u5053 = KTree.node A10K2.u5051 (nat_lit 77748525) (nat_lit 6651382109) (nat_lit 0) A10K2.u5052 from rfl, allE_node, arows5051, irow5053, arows5052]
  all_goals rfl

theorem atot5053 : totK PA10K2 A10K2.u5053 = [0, 539891055239, 3824703565372, 7934181974769, 5552799125607, 1096736172776, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u5053 = KTree.node A10K2.u5051 (nat_lit 77748525) (nat_lit 6651382109) (nat_lit 0) A10K2.u5052 from rfl, totK_node, atot5051, atot5052]
  decide +kernel

theorem arows5056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5056 = true := by
  rw [show A10K2.u5056 = KTree.node A10K2.u5054 (nat_lit 77776964) (nat_lit 11710074203) (nat_lit 0) A10K2.u5055 from rfl, allE_node, arows5054, irow5056, arows5055]
  all_goals rfl

theorem atot5056 : totK PA10K2 A10K2.u5056 = [0, 306130628101, 2086330268748, 5977300298303, 7247953811949, 2770087436086, 348076541537, 6354482628, 0, 0] := by
  rw [show A10K2.u5056 = KTree.node A10K2.u5054 (nat_lit 77776964) (nat_lit 11710074203) (nat_lit 0) A10K2.u5055 from rfl, totK_node, atot5054, atot5055]
  decide +kernel

theorem arows5060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5060 = true := by
  rw [show A10K2.u5060 = KTree.node A10K2.u5058 (nat_lit 77798153) (nat_lit 8504150638) (nat_lit 0) A10K2.u5059 from rfl, allE_node, arows5058, irow5060, arows5059]
  all_goals rfl

theorem atot5060 : totK PA10K2 A10K2.u5060 = [0, 1057749846530, 5118823237580, 8198506650191, 4642649983607, 821522576959, 37664216019, 0, 0, 0] := by
  rw [show A10K2.u5060 = KTree.node A10K2.u5058 (nat_lit 77798153) (nat_lit 8504150638) (nat_lit 0) A10K2.u5059 from rfl, totK_node, atot5058, atot5059]
  decide +kernel

theorem arows5063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5063 = true := by
  rw [show A10K2.u5063 = KTree.node A10K2.u5061 (nat_lit 77827532) (nat_lit 6322575519) (nat_lit 0) A10K2.u5062 from rfl, allE_node, arows5061, irow5063, arows5062]
  all_goals rfl

theorem atot5063 : totK PA10K2 A10K2.u5063 = [0, 0, 1545691604077, 6353908811228, 8174613184146, 3363638492065, 383083509072, 6904928264, 0, 0] := by
  rw [show A10K2.u5063 = KTree.node A10K2.u5061 (nat_lit 77827532) (nat_lit 6322575519) (nat_lit 0) A10K2.u5062 from rfl, totK_node, atot5061, atot5062]
  decide +kernel

theorem arows5068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5068 = true := by
  rw [show A10K2.u5068 = KTree.node A10K2.u5066 (nat_lit 78196372) (nat_lit 10746150214) (nat_lit 0) A10K2.u5067 from rfl, allE_node, arows5066, irow5068, arows5067]
  all_goals rfl

theorem atot5068 : totK PA10K2 A10K2.u5068 = [0, 1015923028415, 4675533935453, 7451202722488, 4888655112768, 1212125119713, 82657267325, 0, 0, 0] := by
  rw [show A10K2.u5068 = KTree.node A10K2.u5066 (nat_lit 78196372) (nat_lit 10746150214) (nat_lit 0) A10K2.u5067 from rfl, totK_node, atot5066, atot5067]
  decide +kernel

theorem arows5071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5071 = true := by
  rw [show A10K2.u5071 = KTree.node A10K2.u5069 (nat_lit 78207318) (nat_lit 8611895978) (nat_lit 0) A10K2.u5070 from rfl, allE_node, arows5069, irow5071, arows5070]
  all_goals rfl

theorem atot5071 : totK PA10K2 A10K2.u5071 = [0, 1207602960733, 5536787534775, 8244540050766, 4055345715098, 517073572872, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5071 = KTree.node A10K2.u5069 (nat_lit 78207318) (nat_lit 8611895978) (nat_lit 0) A10K2.u5070 from rfl, totK_node, atot5069, atot5070]
  decide +kernel

theorem arows5075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5075 = true := by
  rw [show A10K2.u5075 = KTree.node A10K2.u5073 (nat_lit 78228694) (nat_lit 15177660555) (nat_lit 0) A10K2.u5074 from rfl, allE_node, arows5073, irow5075, arows5074]
  all_goals rfl

theorem atot5075 : totK PA10K2 A10K2.u5075 = [0, 0, 1272079524939, 5537793430125, 7823820516359, 3856121996334, 640995025024, 31082886609, 0, 0] := by
  rw [show A10K2.u5075 = KTree.node A10K2.u5073 (nat_lit 78228694) (nat_lit 15177660555) (nat_lit 0) A10K2.u5074 from rfl, totK_node, atot5073, atot5074]
  decide +kernel

theorem arows5078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5078 = true := by
  rw [show A10K2.u5078 = KTree.node A10K2.u5076 (nat_lit 78240040) (nat_lit 11685777047) (nat_lit 0) A10K2.u5077 from rfl, allE_node, arows5076, irow5078, arows5077]
  all_goals rfl

theorem atot5078 : totK PA10K2 A10K2.u5078 = [0, 272465788330, 2116531084954, 6120833829486, 7429129125480, 2972289497046, 294743465130, 6121173289, 0, 0] := by
  rw [show A10K2.u5078 = KTree.node A10K2.u5076 (nat_lit 78240040) (nat_lit 11685777047) (nat_lit 0) A10K2.u5077 from rfl, totK_node, atot5076, atot5077]
  decide +kernel

theorem arows5084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5084 = true := by
  rw [show A10K2.u5084 = KTree.node A10K2.u5082 (nat_lit 78259711) (nat_lit 13798293390) (nat_lit 0) A10K2.u5083 from rfl, allE_node, arows5082, irow5084, arows5083]
  all_goals rfl

theorem atot5084 : totK PA10K2 A10K2.u5084 = [0, 1063163581800, 4970658585867, 7802291934185, 4423184090462, 866692910611, 56136589318, 0, 0, 0] := by
  rw [show A10K2.u5084 = KTree.node A10K2.u5082 (nat_lit 78259711) (nat_lit 13798293390) (nat_lit 0) A10K2.u5083 from rfl, totK_node, atot5082, atot5083]
  decide +kernel

theorem arows5087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5087 = true := by
  rw [show A10K2.u5087 = KTree.node A10K2.u5085 (nat_lit 78268769) (nat_lit 8951841821) (nat_lit 0) A10K2.u5086 from rfl, allE_node, arows5085, irow5087, arows5086]
  all_goals rfl

theorem atot5087 : totK PA10K2 A10K2.u5087 = [0, 817664287946, 4458987268639, 7860746048793, 4873694369665, 845863924683, 37592353370, 0, 0, 0] := by
  rw [show A10K2.u5087 = KTree.node A10K2.u5085 (nat_lit 78268769) (nat_lit 8951841821) (nat_lit 0) A10K2.u5086 from rfl, totK_node, atot5085, atot5086]
  decide +kernel

theorem arows5091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5091 = true := by
  rw [show A10K2.u5091 = KTree.node A10K2.u5089 (nat_lit 78299144) (nat_lit 14494373409) (nat_lit 0) A10K2.u5090 from rfl, allE_node, arows5089, irow5091, arows5090]
  all_goals rfl

theorem atot5091 : totK PA10K2 A10K2.u5091 = [0, 0, 1774960723073, 6984464702286, 7819425461206, 2230719070181, 148096627338, 0, 0, 0] := by
  rw [show A10K2.u5091 = KTree.node A10K2.u5089 (nat_lit 78299144) (nat_lit 14494373409) (nat_lit 0) A10K2.u5090 from rfl, totK_node, atot5089, atot5090]
  decide +kernel

theorem arows5094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5094 = true := by
  rw [show A10K2.u5094 = KTree.node A10K2.u5092 (nat_lit 78327443) (nat_lit 10854363860) (nat_lit 0) A10K2.u5093 from rfl, allE_node, arows5092, irow5094, arows5093]
  all_goals rfl

theorem atot5094 : totK PA10K2 A10K2.u5094 = [0, 1061690136320, 4553839183541, 7049836569385, 5008364750045, 1690645505827, 245165146957, 6354482628, 0, 0] := by
  rw [show A10K2.u5094 = KTree.node A10K2.u5092 (nat_lit 78327443) (nat_lit 10854363860) (nat_lit 0) A10K2.u5093 from rfl, totK_node, atot5092, atot5093]
  decide +kernel

theorem arows5099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5099 = true := by
  rw [show A10K2.u5099 = KTree.node A10K2.u5097 (nat_lit 78357728) (nat_lit 5143285892) (nat_lit 0) A10K2.u5098 from rfl, allE_node, arows5097, irow5099, arows5098]
  all_goals rfl

theorem atot5099 : totK PA10K2 A10K2.u5099 = [0, 307423764049, 2609366278831, 6878802073205, 7148882016984, 2818477591771, 338800869035, 7047025452, 0, 0] := by
  rw [show A10K2.u5099 = KTree.node A10K2.u5097 (nat_lit 78357728) (nat_lit 5143285892) (nat_lit 0) A10K2.u5098 from rfl, totK_node, atot5097, atot5098]
  decide +kernel

theorem arows5102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5102 = true := by
  rw [show A10K2.u5102 = KTree.node A10K2.u5100 (nat_lit 78643720) (nat_lit 14460220229) (nat_lit 0) A10K2.u5101 from rfl, allE_node, arows5100, irow5102, arows5101]
  all_goals rfl

theorem atot5102 : totK PA10K2 A10K2.u5102 = [0, 799194905149, 3920749209584, 7111591179773, 5732963554285, 1801919650425, 130740567223, 0, 0, 0] := by
  rw [show A10K2.u5102 = KTree.node A10K2.u5100 (nat_lit 78643720) (nat_lit 14460220229) (nat_lit 0) A10K2.u5101 from rfl, totK_node, atot5100, atot5101]
  decide +kernel

theorem arows5106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5106 = true := by
  rw [show A10K2.u5106 = KTree.node A10K2.u5104 (nat_lit 78661996) (nat_lit 12782193965) (nat_lit 0) A10K2.u5105 from rfl, allE_node, arows5104, irow5106, arows5105]
  all_goals rfl

theorem atot5106 : totK PA10K2 A10K2.u5106 = [0, 1212796082426, 5357860389106, 7907995786561, 3999646233668, 543714724010, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u5106 = KTree.node A10K2.u5104 (nat_lit 78661996) (nat_lit 12782193965) (nat_lit 0) A10K2.u5105 from rfl, totK_node, atot5104, atot5105]
  decide +kernel

theorem arows5109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5109 = true := by
  rw [show A10K2.u5109 = KTree.node A10K2.u5107 (nat_lit 78678528) (nat_lit 15366970878) (nat_lit 0) A10K2.u5108 from rfl, allE_node, arows5107, irow5109, arows5108]
  all_goals rfl

theorem atot5109 : totK PA10K2 A10K2.u5109 = [0, 17179869184, 1731387656040, 6248587985288, 7443050674049, 3056760312623, 486401749467, 30220878370, 0, 0] := by
  rw [show A10K2.u5109 = KTree.node A10K2.u5107 (nat_lit 78678528) (nat_lit 15366970878) (nat_lit 0) A10K2.u5108 from rfl, totK_node, atot5107, atot5108]
  decide +kernel

theorem arows5120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5120 = true := by
  rw [show A10K2.u5120 = KTree.node A10K2.u5118 (nat_lit 78698725) (nat_lit 7101057036) (nat_lit 0) A10K2.u5119 from rfl, allE_node, arows5118, irow5120, arows5119]
  all_goals rfl

theorem atot5120 : totK PA10K2 A10K2.u5120 = [0, 477404030452, 2614154079832, 6360963688767, 6961333853953, 2445621093059, 251946617966, 5546304973, 0, 0] := by
  rw [show A10K2.u5120 = KTree.node A10K2.u5118 (nat_lit 78698725) (nat_lit 7101057036) (nat_lit 0) A10K2.u5119 from rfl, totK_node, atot5118, atot5119]
  decide +kernel

theorem arows5123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5123 = true := by
  rw [show A10K2.u5123 = KTree.node A10K2.u5121 (nat_lit 78724244) (nat_lit 10531802714) (nat_lit 0) A10K2.u5122 from rfl, allE_node, arows5121, irow5123, arows5122]
  all_goals rfl

theorem atot5123 : totK PA10K2 A10K2.u5123 = [0, 1109369601048, 5250118546677, 7861044686108, 4138420257878, 691785695430, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5123 = KTree.node A10K2.u5121 (nat_lit 78724244) (nat_lit 10531802714) (nat_lit 0) A10K2.u5122 from rfl, totK_node, atot5121, atot5122]
  decide +kernel

theorem arows5127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5127 = true := by
  rw [show A10K2.u5127 = KTree.node A10K2.u5125 (nat_lit 78738787) (nat_lit 9354519032) (nat_lit 0) A10K2.u5126 from rfl, allE_node, arows5125, irow5127, arows5126]
  all_goals rfl

theorem atot5127 : totK PA10K2 A10K2.u5127 = [0, 461607179050, 3538853368399, 8012916701465, 6070596242905, 1266825856509, 51804136795, 0, 0, 0] := by
  rw [show A10K2.u5127 = KTree.node A10K2.u5125 (nat_lit 78738787) (nat_lit 9354519032) (nat_lit 0) A10K2.u5126 from rfl, totK_node, atot5125, atot5126]
  decide +kernel

theorem arows5130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5130 = true := by
  rw [show A10K2.u5130 = KTree.node A10K2.u5128 (nat_lit 78759198) (nat_lit 10947917954) (nat_lit 0) A10K2.u5129 from rfl, allE_node, arows5128, irow5130, arows5129]
  all_goals rfl

theorem atot5130 : totK PA10K2 A10K2.u5130 = [0, 0, 780839573092, 4710350794343, 8179213357321, 4305076656878, 702852311225, 30647824416, 0, 0] := by
  rw [show A10K2.u5130 = KTree.node A10K2.u5128 (nat_lit 78759198) (nat_lit 10947917954) (nat_lit 0) A10K2.u5129 from rfl, totK_node, atot5128, atot5129]
  decide +kernel

theorem arows5135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5135 = true := by
  rw [show A10K2.u5135 = KTree.node A10K2.u5133 (nat_lit 78777171) (nat_lit 8816815782) (nat_lit 0) A10K2.u5134 from rfl, allE_node, arows5133, irow5135, arows5134]
  all_goals rfl

theorem atot5135 : totK PA10K2 A10K2.u5135 = [0, 1030440286844, 4649133263446, 7494621028369, 4877265098852, 1029762215591, 58082665913, 0, 0, 0] := by
  rw [show A10K2.u5135 = KTree.node A10K2.u5133 (nat_lit 78777171) (nat_lit 8816815782) (nat_lit 0) A10K2.u5134 from rfl, totK_node, atot5133, atot5134]
  decide +kernel

theorem arows5138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5138 = true := by
  rw [show A10K2.u5138 = KTree.node A10K2.u5136 (nat_lit 78788876) (nat_lit 11950738972) (nat_lit 0) A10K2.u5137 from rfl, allE_node, arows5136, irow5138, arows5137]
  all_goals rfl

theorem atot5138 : totK PA10K2 A10K2.u5138 = [0, 1302508846857, 5502461393872, 7690034588779, 3941142615480, 627776003630, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5138 = KTree.node A10K2.u5136 (nat_lit 78788876) (nat_lit 11950738972) (nat_lit 0) A10K2.u5137 from rfl, totK_node, atot5136, atot5137]
  decide +kernel

theorem arows5142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5142 = true := by
  rw [show A10K2.u5142 = KTree.node A10K2.u5140 (nat_lit 78809128) (nat_lit 12645193567) (nat_lit 0) A10K2.u5141 from rfl, allE_node, arows5140, irow5142, arows5141]
  all_goals rfl

theorem atot5142 : totK PA10K2 A10K2.u5142 = [0, 0, 2500366851546, 7952377240663, 6881918834052, 1510259515935, 77177557509, 0, 0, 0] := by
  rw [show A10K2.u5142 = KTree.node A10K2.u5140 (nat_lit 78809128) (nat_lit 12645193567) (nat_lit 0) A10K2.u5141 from rfl, totK_node, atot5140, atot5141]
  decide +kernel

theorem arows5145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5145 = true := by
  rw [show A10K2.u5145 = KTree.node A10K2.u5143 (nat_lit 78827564) (nat_lit 12812578913) (nat_lit 0) A10K2.u5144 from rfl, allE_node, arows5143, irow5145, arows5144]
  all_goals rfl

theorem atot5145 : totK PA10K2 A10K2.u5145 = [0, 0, 1502411033815, 6274402419416, 7825973945647, 2851205147349, 348162649300, 6354482628, 0, 0] := by
  rw [show A10K2.u5145 = KTree.node A10K2.u5143 (nat_lit 78827564) (nat_lit 12812578913) (nat_lit 0) A10K2.u5144 from rfl, totK_node, atot5143, atot5144]
  decide +kernel

theorem arows5151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5151 = true := by
  rw [show A10K2.u5151 = KTree.node A10K2.u5149 (nat_lit 78921824) (nat_lit 13847045638) (nat_lit 0) A10K2.u5150 from rfl, allE_node, arows5149, irow5151, arows5150]
  all_goals rfl

theorem atot5151 : totK PA10K2 A10K2.u5151 = [0, 0, 998241710667, 5122685510927, 8095348809241, 3929969952575, 577454468138, 30388749007, 0, 0] := by
  rw [show A10K2.u5151 = KTree.node A10K2.u5149 (nat_lit 78921824) (nat_lit 13847045638) (nat_lit 0) A10K2.u5150 from rfl, totK_node, atot5149, atot5150]
  decide +kernel

theorem arows5154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5154 = true := by
  rw [show A10K2.u5154 = KTree.node A10K2.u5152 (nat_lit 78980949) (nat_lit 6554109619) (nat_lit 0) A10K2.u5153 from rfl, allE_node, arows5152, irow5154, arows5153]
  all_goals rfl

theorem atot5154 : totK PA10K2 A10K2.u5154 = [0, 0, 1259537940028, 5433544748048, 7877427813707, 3848952001060, 604497759393, 31653953727, 0, 0] := by
  rw [show A10K2.u5154 = KTree.node A10K2.u5152 (nat_lit 78980949) (nat_lit 6554109619) (nat_lit 0) A10K2.u5153 from rfl, totK_node, atot5152, atot5153]
  decide +kernel

theorem arows5158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5158 = true := by
  rw [show A10K2.u5158 = KTree.node A10K2.u5156 (nat_lit 78991623) (nat_lit 6886156202) (nat_lit 0) A10K2.u5157 from rfl, allE_node, arows5156, irow5158, arows5157]
  all_goals rfl

theorem atot5158 : totK PA10K2 A10K2.u5158 = [0, 0, 1382032412180, 5821131170244, 7869853202031, 3534829978239, 481527087359, 12072523186, 0, 0] := by
  rw [show A10K2.u5158 = KTree.node A10K2.u5156 (nat_lit 78991623) (nat_lit 6886156202) (nat_lit 0) A10K2.u5157 from rfl, totK_node, atot5156, atot5157]
  decide +kernel

theorem arows5161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5161 = true := by
  rw [show A10K2.u5161 = KTree.node A10K2.u5159 (nat_lit 79042728) (nat_lit 8751241636) (nat_lit 0) A10K2.u5160 from rfl, allE_node, arows5159, irow5161, arows5160]
  all_goals rfl

theorem atot5161 : totK PA10K2 A10K2.u5161 = [0, 0, 1334726823222, 5757488403510, 7733941234907, 3308214757306, 514014271795, 30074883546, 0, 0] := by
  rw [show A10K2.u5161 = KTree.node A10K2.u5159 (nat_lit 79042728) (nat_lit 8751241636) (nat_lit 0) A10K2.u5160 from rfl, totK_node, atot5159, atot5160]
  decide +kernel

theorem arows5166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5166 = true := by
  rw [show A10K2.u5166 = KTree.node A10K2.u5164 (nat_lit 79054487) (nat_lit 12084326520) (nat_lit 0) A10K2.u5165 from rfl, allE_node, arows5164, irow5166, arows5165]
  all_goals rfl

theorem atot5166 : totK PA10K2 A10K2.u5166 = [0, 0, 844597474735, 4590598021999, 7894127211060, 4445353520123, 791700199728, 37357927314, 0, 0] := by
  rw [show A10K2.u5166 = KTree.node A10K2.u5164 (nat_lit 79054487) (nat_lit 12084326520) (nat_lit 0) A10K2.u5165 from rfl, totK_node, atot5164, atot5165]
  decide +kernel

theorem arows5169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5169 = true := by
  rw [show A10K2.u5169 = KTree.node A10K2.u5167 (nat_lit 79079702) (nat_lit 9854604557) (nat_lit 0) A10K2.u5168 from rfl, allE_node, arows5167, irow5169, arows5168]
  all_goals rfl

theorem atot5169 : totK PA10K2 A10K2.u5169 = [0, 0, 0, 2220910292753, 7581953775490, 6716998398789, 1686253704422, 112993531056, 0, 0] := by
  rw [show A10K2.u5169 = KTree.node A10K2.u5167 (nat_lit 79079702) (nat_lit 9854604557) (nat_lit 0) A10K2.u5168 from rfl, totK_node, atot5167, atot5168]
  decide +kernel

theorem arows5173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5173 = true := by
  rw [show A10K2.u5173 = KTree.node A10K2.u5171 (nat_lit 83888428) (nat_lit 13491528489) (nat_lit 0) A10K2.u5172 from rfl, allE_node, arows5171, irow5173, arows5172]
  all_goals rfl

theorem atot5173 : totK PA10K2 A10K2.u5173 = [0, 869984120561, 3774547346624, 5561988274500, 3956756465828, 2908604547595, 1554913632104, 265614550179, 6354482628, 0] := by
  rw [show A10K2.u5173 = KTree.node A10K2.u5171 (nat_lit 83888428) (nat_lit 13491528489) (nat_lit 0) A10K2.u5172 from rfl, totK_node, atot5171, atot5172]
  decide +kernel

theorem arows5176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5176 = true := by
  rw [show A10K2.u5176 = KTree.node A10K2.u5174 (nat_lit 83906881) (nat_lit 10155128821) (nat_lit 0) A10K2.u5175 from rfl, allE_node, arows5174, irow5176, arows5175]
  all_goals rfl

theorem atot5176 : totK PA10K2 A10K2.u5176 = [0, 1468708863261, 5984479197580, 7855346163010, 3396580511833, 407403566767, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5176 = KTree.node A10K2.u5174 (nat_lit 83906881) (nat_lit 10155128821) (nat_lit 0) A10K2.u5175 from rfl, totK_node, atot5174, atot5175]
  decide +kernel

theorem arows5183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5183 = true := by
  rw [show A10K2.u5183 = KTree.node A10K2.u5181 (nat_lit 83919117) (nat_lit 5875885541) (nat_lit 0) A10K2.u5182 from rfl, allE_node, arows5181, irow5183, arows5182]
  all_goals rfl

theorem atot5183 : totK PA10K2 A10K2.u5183 = [0, 0, 1971046560889, 7089822990621, 7680482703895, 2526011263996, 244897207896, 14945844243, 0, 0] := by
  rw [show A10K2.u5183 = KTree.node A10K2.u5181 (nat_lit 83919117) (nat_lit 5875885541) (nat_lit 0) A10K2.u5182 from rfl, totK_node, atot5181, atot5182]
  decide +kernel

theorem arows5186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5186 = true := by
  rw [show A10K2.u5186 = KTree.node A10K2.u5184 (nat_lit 83937467) (nat_lit 3676558856) (nat_lit 0) A10K2.u5185 from rfl, allE_node, arows5184, irow5186, arows5185]
  all_goals rfl

theorem atot5186 : totK PA10K2 A10K2.u5186 = [0, 0, 1163204608389, 5280318065338, 7761074643987, 3898822161993, 625184975335, 21250956960, 0, 0] := by
  rw [show A10K2.u5186 = KTree.node A10K2.u5184 (nat_lit 83937467) (nat_lit 3676558856) (nat_lit 0) A10K2.u5185 from rfl, totK_node, atot5184, atot5185]
  decide +kernel

theorem arows5190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5190 = true := by
  rw [show A10K2.u5190 = KTree.node A10K2.u5188 (nat_lit 84020260) (nat_lit 12638850083) (nat_lit 0) A10K2.u5189 from rfl, allE_node, arows5188, irow5190, arows5189]
  all_goals rfl

theorem atot5190 : totK PA10K2 A10K2.u5190 = [0, 999035484426, 4549812140359, 7433537502364, 5116151570296, 1270430586080, 73430970193, 0, 0, 0] := by
  rw [show A10K2.u5190 = KTree.node A10K2.u5188 (nat_lit 84020260) (nat_lit 12638850083) (nat_lit 0) A10K2.u5189 from rfl, totK_node, atot5188, atot5189]
  decide +kernel

theorem arows5193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5193 = true := by
  rw [show A10K2.u5193 = KTree.node A10K2.u5191 (nat_lit 84034102) (nat_lit 13359531043) (nat_lit 0) A10K2.u5192 from rfl, allE_node, arows5191, irow5193, arows5192]
  all_goals rfl

theorem atot5193 : totK PA10K2 A10K2.u5193 = [0, 1057405987564, 5148154143075, 7880890463531, 4001602959989, 637668200086, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5193 = KTree.node A10K2.u5191 (nat_lit 84034102) (nat_lit 13359531043) (nat_lit 0) A10K2.u5192 from rfl, totK_node, atot5191, atot5192]
  decide +kernel

theorem arows5198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5198 = true := by
  rw [show A10K2.u5198 = KTree.node A10K2.u5196 (nat_lit 84059370) (nat_lit 12532643617) (nat_lit 0) A10K2.u5197 from rfl, allE_node, arows5196, irow5198, arows5197]
  all_goals rfl

theorem atot5198 : totK PA10K2 A10K2.u5198 = [0, 0, 1998120558490, 7283257745941, 7569138605038, 2058487090333, 127875982085, 0, 0, 0] := by
  rw [show A10K2.u5198 = KTree.node A10K2.u5196 (nat_lit 84059370) (nat_lit 12532643617) (nat_lit 0) A10K2.u5197 from rfl, totK_node, atot5196, atot5197]
  decide +kernel

theorem arows5201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5201 = true := by
  rw [show A10K2.u5201 = KTree.node A10K2.u5199 (nat_lit 84083525) (nat_lit 6319932568) (nat_lit 0) A10K2.u5200 from rfl, allE_node, arows5199, irow5201, arows5200]
  all_goals rfl

theorem atot5201 : totK PA10K2 A10K2.u5201 = [0, 809589589006, 3636092492929, 6567099038120, 5685325796953, 2130246089103, 291124564400, 6354482628, 0, 0] := by
  rw [show A10K2.u5201 = KTree.node A10K2.u5199 (nat_lit 84083525) (nat_lit 6319932568) (nat_lit 0) A10K2.u5200 from rfl, totK_node, atot5199, atot5200]
  decide +kernel

theorem arows5205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5205 = true := by
  rw [show A10K2.u5205 = KTree.node A10K2.u5203 (nat_lit 84108672) (nat_lit 14352822343) (nat_lit 0) A10K2.u5204 from rfl, allE_node, arows5203, irow5205, arows5204]
  all_goals rfl

theorem atot5205 : totK PA10K2 A10K2.u5205 = [0, 1078827900697, 5177727474490, 8293274919811, 4903822173914, 818545655271, 19275683512, 0, 0, 0] := by
  rw [show A10K2.u5205 = KTree.node A10K2.u5203 (nat_lit 84108672) (nat_lit 14352822343) (nat_lit 0) A10K2.u5204 from rfl, totK_node, atot5203, atot5204]
  decide +kernel

theorem arows5208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5208 = true := by
  rw [show A10K2.u5208 = KTree.node A10K2.u5206 (nat_lit 84119194) (nat_lit 11648378353) (nat_lit 0) A10K2.u5207 from rfl, allE_node, arows5206, irow5208, arows5207]
  all_goals rfl

theorem atot5208 : totK PA10K2 A10K2.u5208 = [0, 0, 1253950174212, 5729009194591, 8337443637320, 3965824763508, 457323876347, 6904928264, 0, 0] := by
  rw [show A10K2.u5208 = KTree.node A10K2.u5206 (nat_lit 84119194) (nat_lit 11648378353) (nat_lit 0) A10K2.u5207 from rfl, totK_node, atot5206, atot5207]
  decide +kernel

end QECKChecks.A10K2
